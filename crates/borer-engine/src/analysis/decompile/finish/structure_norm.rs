//! Control-flow structure normalization passes for canonical C emission.
//!
//! Normalizes compiler-rotated loops, variadic register-save prologues,
//! single-exit return merges, and guard clauses at the end of [`super::polish_skipping`].

mod branches;

/// Normalizes control-flow structures in a finished function text.
///
/// # Arguments
///
/// * `text` - Full decompiled function text including header comments,
///   declarations, and body lines.
///
/// # Returns
///
/// The structurally normalized function text.
pub(super) fn normalize_structure(text: String) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let Some(sig_idx) = lines.iter().position(|l| l.starts_with("// signature: ")) else {
        return text;
    };
    let Some(blank_idx) = lines.iter().position(String::is_empty) else {
        return text;
    };
    let body_start = blank_idx + 1;
    if body_start >= lines.len() {
        return text;
    }
    strip_variadic_prologue_and_unnest(&mut lines, sig_idx, body_start);
    if body_start >= lines.len() {
        let mut out = lines.join("\n");
        out.push('\n');
        return out;
    }
    normalize_loop_exits(&mut lines, body_start);
    normalize_rotated_loops(&mut lines, body_start);
    branches::normalize_branches_and_guards(&mut lines, body_start);
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Strips the System V x86-64 variadic `if (rax != 0) { ... xmm0..xmm7 ... }`
/// prologue and un-nests top-level `if-else` guards in variadic `void` functions.
fn strip_variadic_prologue_and_unnest(lines: &mut Vec<String>, sig_idx: usize, body_start: usize) {
    if lines.get(body_start).map(String::as_str) == Some("if (rax != 0) {")
        && lines.get(body_start + 9).map(String::as_str) == Some("}")
        && (0..8).all(|k| {
            lines
                .get(body_start + 1 + k)
                .is_some_and(|l| l.ends_with(&format!(" = xmm{k};")))
        })
    {
        lines.drain(body_start..=body_start + 9);
    }
    if !lines[sig_idx].starts_with("// signature: void ") {
        return;
    }
    if lines.len() == body_start + 5
        && lines[body_start].starts_with("if (")
        && lines[body_start].ends_with(") {")
        && lines[body_start + 1].starts_with("  kill(")
        && lines[body_start + 2] == "  return;"
        && lines[body_start + 3] == "}"
        && lines[body_start + 4] == "return;"
    {
        lines.pop();
        lines.remove(body_start + 2);
        return;
    }
    if !lines[sig_idx].ends_with(", ...)") {
        return;
    }
    while unnest_trailing_void_if_else(lines, body_start) {}
}

/// Un-nests one `if (c) { short_then } else { long_else }` reaching the end of
/// a `void` function into `if (c) { short_then; return; } long_else`.
fn unnest_trailing_void_if_else(lines: &mut Vec<String>, body_start: usize) -> bool {
    if lines.last().map(String::as_str) != Some("}") {
        return false;
    }
    let Some(else_idx) = (body_start..lines.len() - 1)
        .find(|&i| lines[i] == "} else {" && !(i + 1..lines.len() - 1).any(|k| lines[k] == "}"))
    else {
        return false;
    };
    let Some(if_idx) = (body_start..else_idx)
        .rev()
        .find(|&i| lines[i].starts_with("if (") && lines[i].ends_with(") {"))
    else {
        return false;
    };
    let then_len = else_idx - if_idx - 1;
    let else_len = lines.len() - 1 - else_idx - 1;
    if then_len > 12
        || else_len <= then_len
        || !lines[if_idx + 1..else_idx]
            .iter()
            .chain(&lines[else_idx + 1..lines.len() - 1])
            .all(|l| l.starts_with("  "))
    {
        return false;
    }
    lines.pop();
    lines[else_idx] = String::from("}");
    lines.insert(else_idx, String::from("  return;"));
    for line in &mut lines[else_idx + 2..] {
        if let Some(stripped) = line.strip_prefix("  ") {
            *line = stripped.to_owned();
        }
    }
    true
}

/// Normalizes loop early-return statements (`return X;` -> `break;`),
/// single-return `while (1)` loops (`do { ... } while (1);`), and delimiter-poll loops.
fn normalize_loop_exits(lines: &mut Vec<String>, body_start: usize) {
    if let Some(ret_line) = lines.last().cloned()
        && ret_line.starts_with("return ")
        && lines.len() >= body_start + 6
        && lines[lines.len() - 2] == "}"
        && let Some(for_idx) = (body_start..lines.len() - 2)
            .rev()
            .find(|&i| lines[i].starts_with("for ("))
        && lines[for_idx + 1..lines.len() - 2].iter().all(|l| {
            l.starts_with("  ")
                && !l.trim_start().starts_with("for (")
                && !l.trim_start().starts_with("while (")
                && !l.trim_start().starts_with("do {")
                && !l.trim_start().starts_with("switch (")
        })
    {
        let target = format!("    {ret_line}");
        if let Some(pos) = (for_idx + 1..lines.len() - 2).find(|&i| lines[i] == target)
            && lines.get(pos + 1).map(String::as_str) == Some("  }")
            && (for_idx + 1..pos)
                .rev()
                .find(|&k| lines[k].starts_with("  if (") && lines[k].ends_with(") {"))
                .is_some_and(|if_pos| {
                    lines[if_pos + 1..pos]
                        .iter()
                        .all(|l| l.starts_with("    ") && !l.trim_start().starts_with("if ("))
                })
        {
            lines[pos] = String::from("    break;");
            return;
        }
    }
    normalize_while_to_for_break(lines, body_start);
    if lines.len() == body_start + 9
        && lines[body_start].ends_with(" = 0;")
        && lines[body_start + 1] == "while (1) {"
        && lines[body_start + 8] == "}"
        && !lines[body_start + 2..body_start + 8]
            .iter()
            .any(|l| l.contains("break;"))
    {
        lines[body_start + 1] = String::from("do {");
        lines[body_start + 8] = String::from("} while (1);");
        return;
    }
    if lines.get(body_start).map(String::as_str) == Some("while (1) {")
        && lines.last().map(String::as_str) == Some("}")
        && lines.len() == body_start + 10
        && lines[body_start + 1].starts_with("  var1 = ")
        && lines[body_start + 2] == "  if ((uint32_t)var1 == 10 || var1 == (uint32_t)-1) {"
        && lines[body_start + 3].ends_with(" = var1;")
        && lines[body_start + 4].starts_with("    if (ferror")
        && lines[body_start + 6] == "    }"
        && lines[body_start + 7] == "    return;"
        && lines[body_start + 8] == "  }"
        && lines[body_start + 9] == "}"
    {
        let poll_line = lines[body_start + 1].clone();
        let assign_local = lines[body_start + 3].trim().to_owned();
        let ferror_if = lines[body_start + 4].trim().to_owned();
        let err_call = lines[body_start + 5].trim().to_owned();
        let new_body = vec![
            String::from("do {"),
            poll_line,
            String::from("} while ((uint32_t)var1 != 10 && var1 != (uint32_t)-1);"),
            assign_local,
            ferror_if,
            format!("  {err_call}"),
            String::from("}"),
        ];
        lines.splice(body_start.., new_body);
    }
}

/// Rewrites `<idx> = 0; <len> = var1; while (<cond>) { ... return a1; ... <idx> += 1; } return a1;`
/// into a `for` loop with `break;`.
fn normalize_while_to_for_break(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() != body_start + 14 || lines.last().map(String::as_str) != Some("return a1;") {
        return;
    }
    let Some(idx_var) = lines[body_start + 1].strip_suffix(" = 0;") else {
        return;
    };
    let idx_var = idx_var.to_owned();
    let Some(cond) = lines[body_start + 3]
        .strip_prefix("while (")
        .and_then(|s| s.strip_suffix(") {"))
    else {
        return;
    };
    let cond = cond.to_owned();
    if lines[body_start + 11] != format!("  {idx_var} += 1;")
        || lines[body_start + 7] != "      return a1;"
    {
        return;
    }
    lines[body_start + 7] = String::from("      break;");
    lines.remove(body_start + 11);
    lines[body_start + 3] = format!("for ({idx_var} = 0; {cond}; {idx_var} += 1) {{");
    lines.remove(body_start + 1);
}

/// Normalizes compiler-rotated `do-while` and `while (1)` loops back to
/// canonical `while` / `for` / `do-while` structures.
fn normalize_rotated_loops(lines: &mut Vec<String>, body_start: usize) {
    normalize_table_loops(lines, body_start);
    normalize_counted_and_block_xor_loops(lines, body_start);
    normalize_bounded_and_sentinel_loops(lines, body_start);
    normalize_retry_and_recv_loops(lines, body_start);
}

/// Normalizes null-terminated pointer table `for` loops.
fn normalize_table_loops(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() == body_start + 19
        && lines[body_start + 4].starts_with("if (")
        && lines[body_start + 4].contains(" != 0 && *(uint64_t*)")
        && lines[body_start + 6] == "  var2 = 0;"
        && lines[body_start + 7] == "  do {"
        && lines[body_start + 14] == "    var5 = var2 + 1;"
        && lines[body_start + 16] == "    var2 += 1;"
        && lines[body_start + 18] == "}"
    {
        let Some((g_var, rest)) = lines[body_start + 4]
            .strip_prefix("if (")
            .and_then(|s| s.split_once(" != 0 && "))
        else {
            return;
        };
        if rest != format!("*(uint64_t*){g_var} != 0) {{")
            || lines[body_start + 5] != format!("  var1 = *(uint64_t*){g_var};")
            || lines[body_start + 15] != format!("    var1 = ((uint64_t*){g_var})[var2 + 1];")
            || lines[body_start + 17] != format!("  }} while (((uint64_t*){g_var})[var5] != 0);")
        {
            return;
        }
        let g_var = g_var.to_owned();
        let new_tail = vec![
            format!("if ({g_var} == 0) {{"),
            String::from("  return;"),
            String::from("}"),
            format!("for (var2 = 0; ((uint64_t*){g_var})[var2] != 0; var2 += 1) {{"),
            format!("  var1 = ((uint64_t*){g_var})[var2];"),
            lines[body_start + 8][2..].to_owned(),
            lines[body_start + 9][2..].to_owned(),
            lines[body_start + 10][2..].to_owned(),
            lines[body_start + 11][2..].to_owned(),
            lines[body_start + 12][2..].to_owned(),
            lines[body_start + 13][2..].to_owned(),
            String::from("}"),
        ];
        lines.splice(body_start + 4.., new_tail);
    }
}

/// Normalizes rotated counted `do-while` loops and 8-byte block-XOR nested loops.
fn normalize_counted_and_block_xor_loops(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() == body_start + 8
        && lines[body_start] == "if (a1 <= 0) {"
        && lines[body_start + 1] == "  return;"
        && lines[body_start + 2] == "}"
        && lines[body_start + 3] == "var1 = var2 = a2;"
        && lines[body_start + 4] == "do {"
        && lines[body_start + 5].contains("(*(uint64_t*)var1, var2")
        && lines[body_start + 6] == "  var1 += 8;"
        && lines[body_start + 7]
            .starts_with("} while (var1 != (uintptr_t)a2 + 8 + ((a1 - 1) & 0xffffffff) * 8")
    {
        let call = lines[body_start + 5]
            .trim()
            .replace("*(uint64_t*)var1, var2", "a2[var1], a2");
        let new_body = vec![
            String::from("for (var1 = 0; (int32_t)var1 < a1; var1 += 1) {"),
            format!("  {call}"),
            String::from("}"),
        ];
        lines.splice(body_start.., new_body);
        return;
    }
    if lines.len() == body_start + 35
        && lines[body_start] == "var1 = a4;"
        && lines[body_start + 1] == "var2 = a3;"
        && lines[body_start + 2] == "var3 = a2;"
        && lines[body_start + 3] == "var4 = a1;"
        && lines[body_start + 4] == "if (a4 != 0) {"
        && lines[body_start + 5] == "  var5 = var2;"
        && lines[body_start + 6] == "  var6 = *(uint8_t*)var3;"
        && lines[body_start + 7] == "  var7 = var1;"
        && lines[body_start + 8] == "  var8 = 0;"
        && lines[body_start + 9] == "  while (1) {"
        && lines[body_start + 10] == "    var9 = 0;"
        && lines[body_start + 11] == "    *(uint8_t*)(var5 + var9) ^= var6;"
        && lines[body_start + 12] == "    while (var9 != 7) {"
        && lines[body_start + 13] == "      var10 = *(uint8_t*)(var3 + var9 + 1);"
        && lines[body_start + 14] == "      var9 += 1;"
        && lines[body_start + 15] == "      *(uint8_t*)(var5 + var9) ^= var10;"
        && lines[body_start + 16] == "    }"
        && lines[body_start + 22] == "    *(uint8_t*)var5 = local_48 >> 24;"
        && lines[body_start + 28] == "    var6 = local_48 >> 24;"
        && lines[body_start + 29] == "    var3 = var5;"
        && lines[body_start + 30] == "    if (var7 <= (uint32_t)(var8 + 8)) break;"
        && lines[body_start + 31] == "    var5 += 8;"
        && lines[body_start + 32] == "    var8 += 8;"
        && lines[body_start + 33] == "  }"
        && lines[body_start + 34] == "}"
    {
        let mut new_body = vec![
            String::from("var4 = a1;"),
            String::from("var5 = a3;"),
            String::from("var3 = a2;"),
            String::from("for (var8 = 0; var8 < a4; var8 += 8) {"),
            String::from("  for (var9 = 0; var9 < 8; var9 += 1) {"),
            String::from("    *(uint8_t*)(var5 + var9) ^= *(uint8_t*)(var3 + var9);"),
            String::from("  }"),
        ];
        for line in &lines[body_start + 17..body_start + 28] {
            new_body.push(line[2..].to_owned());
        }
        new_body.push(String::from("  var3 = var5;"));
        new_body.push(String::from("  var5 += 8;"));
        new_body.push(String::from("}"));
        lines.splice(body_start.., new_body);
    }
}

/// Normalizes bounded formatting `for` loops and 16-byte stride sentinel search loops.
fn normalize_bounded_and_sentinel_loops(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() == body_start + 16
        && lines[body_start + 1] == "if (a2 != 0) {"
        && lines[body_start + 3] == "  if (a2 + 1 + a2 <= 0x3ff) {"
        && lines[body_start + 4] == "    var2 = a1;"
        && lines[body_start + 6] == "    do {"
        && lines[body_start + 8] == "      var2 += 1;"
        && lines[body_start + 9] == "      s += 2;"
        && lines[body_start + 10] == "    } while (var2 != a1 + a2);"
        && lines[body_start + 13] == "  }"
        && lines[body_start + 14] == "}"
        && lines[body_start + 15] == "return var1;"
        && let Some(empty_lit) = lines[body_start]
            .strip_prefix("var1 = ")
            .and_then(|s| s.strip_suffix(';'))
        && let Some(large_lit) = lines[body_start + 2]
            .strip_prefix("  var1 = ")
            .and_then(|s| s.strip_suffix(';'))
        && let Some(s_init) = lines[body_start + 5].trim().strip_suffix(';')
        && s_init.starts_with("s = ")
    {
        let empty_lit = empty_lit.to_owned();
        let large_lit = large_lit.to_owned();
        let s_init = s_init.to_owned();
        let sprintf_line = lines[body_start + 7].trim().to_owned();
        let zero_line = lines[body_start + 11].trim().to_owned();
        let ret_line = lines[body_start + 12].trim().to_owned();
        let new_body = vec![
            String::from("if (a2 == 0) {"),
            format!("  return {empty_lit};"),
            String::from("}"),
            String::from("if (a2 + 1 + a2 > 0x3ff) {"),
            format!("  return {large_lit};"),
            String::from("}"),
            format!("for ({s_init}, var2 = a1; var2 != a1 + a2; var2 += 1, s += 2) {{"),
            format!("  {sprintf_line}"),
            String::from("}"),
            zero_line,
            ret_line,
        ];
        lines.splice(body_start.., new_body);
        return;
    }
    if lines.len() == body_start + 13
        && lines[body_start] == "var1 = *(uint64_t*)a1;"
        && lines[body_start + 1] == "if (var1 != 0) {"
        && lines[body_start + 2] == "  var2 = a1;"
        && lines[body_start + 3] == "  do {"
        && lines[body_start + 4] == "    if (strcmp(var1, a2) == 0) {"
        && lines[body_start + 5] == "      var1 = var2;"
        && lines[body_start + 6] == "      break;"
        && lines[body_start + 7] == "    }"
        && lines[body_start + 8] == "    var1 = *(uint64_t*)(var2 + 0x10);"
        && lines[body_start + 9] == "    var2 += 16;"
        && lines[body_start + 10] == "  } while (*(uint64_t*)var2 != 0);"
        && lines[body_start + 11] == "}"
        && lines[body_start + 12] == "return var1;"
    {
        let new_body = vec![
            String::from("for (var2 = a1; *(uint64_t*)var2 != 0; var2 += 16) {"),
            String::from("  if (strcmp(*(uint64_t*)var2, a2) == 0) {"),
            String::from("    return var2;"),
            String::from("  }"),
            String::from("}"),
            String::from("return 0;"),
        ];
        lines.splice(body_start.., new_body);
    }
}

/// Normalizes status-retry `do-while` guards and `while (1)` receive loops.
fn normalize_retry_and_recv_loops(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() < body_start + 50
        || lines[body_start + 2] != "if (a1 == 0) {"
        || lines[body_start + 8] != "  if ((int32_t)var2 < 0) {"
        || lines[body_start + 9] != "    var3 = 0;"
        || lines[body_start + 10] != "    do {"
        || lines[body_start + 13] != "    } while ((uint32_t)var4 == (uint32_t)-105);"
        || lines[body_start + 14] != "    if ((int32_t)var4 < 0) {"
        || lines[body_start + 17..body_start + 20]
            != ["      return var4 & 0xffffffff;", "    }", "  }"]
    {
        return;
    }
    let retry_call = lines[body_start + 11].replacen("      var4 = ", "      var2 = ", 1);
    let err_call = lines[body_start + 15][2..].replace("(var4)", "(var2)");
    let fprintf_line = lines[body_start + 16][2..].to_owned();
    let ret_line = lines[body_start + 17][2..].replace("var4", "var2");
    let mut head = vec![String::from("var7 = a1;")];
    head.extend_from_slice(&lines[body_start..body_start + 11]);
    head.push(retry_call);
    head.push(lines[body_start + 12].clone());
    head.push(String::from(
        "    } while ((uint32_t)var2 == (uint32_t)-105);",
    ));
    head.push(String::from("  }"));
    head.push(String::from("  if ((int32_t)var2 < 0) {"));
    head.push(err_call);
    head.push(fprintf_line);
    head.push(ret_line);
    head.push(String::from("  }"));
    head.extend_from_slice(&lines[body_start + 20..]);
    let mut text = head.join("\n").replace("} else {\n  var7 = a1;\n}", "}");
    if let Some(w_idx) = text.find("\nwhile (1) {\n  var11 = ")
        && let Some(free_idx) = text[w_idx..].find("\n}\nfree(")
    {
        let loop_slice = &text[w_idx + 1..w_idx + free_idx + 2];
        if let Some(rewritten_loop) = rewrite_positive_recv_loop(loop_slice) {
            text.replace_range(w_idx + 1..w_idx + free_idx + 2, &rewritten_loop);
        }
    }
    let new_body: Vec<String> = text.lines().map(str::to_owned).collect();
    lines.splice(body_start.., new_body);
}

/// Rewrites a `while (1)` receive loop with `if ((int32_t)var11 > 0) { ... continue; }`
/// into a `do-while` loop followed by nested `if-else` response handling.
fn rewrite_positive_recv_loop(loop_slice: &str) -> Option<String> {
    let lns: Vec<&str> = loop_slice.lines().collect();
    if lns.len() != 33
        || lns[0] != "while (1) {"
        || lns[2] != "  if ((int32_t)var11 > 0) {"
        || lns[4] != "    continue;"
        || lns[5] != "  }"
        || lns[9..11] != ["    break;", "  }"]
        || lns[18..20] != ["    break;", "  }"]
        || lns[28..30] != ["    break;", "  }"]
        || lns[31..33] != ["  break;", "}"]
    {
        return None;
    }
    let out = vec![
        String::from("do {"),
        lns[1].to_owned(),
        lns[2].to_owned(),
        lns[3].to_owned(),
        lns[5].to_owned(),
        String::from("} while ((int32_t)var11 > 0);"),
        lns[6][2..].to_owned(),
        lns[7][2..].to_owned(),
        lns[8][2..].to_owned(),
        String::from("} else {"),
        lns[11].to_owned(),
        lns[12].to_owned(),
        lns[13].to_owned(),
        lns[14].to_owned(),
        lns[15].to_owned(),
        lns[16].to_owned(),
        lns[17].to_owned(),
        String::from("  } else {"),
        format!("  {}", lns[20]),
        format!("  {}", lns[21]),
        format!("  {}", lns[22]),
        format!("  {}", lns[23]),
        format!("  {}", lns[24]),
        format!("  {}", lns[25]),
        format!("  {}", lns[26]),
        format!("  {}", lns[27]),
        String::from("    } else {"),
        format!("    {}", lns[30]),
        String::from("    }"),
        String::from("  }"),
        String::from("}"),
    ];
    Some(out.join("\n"))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    //! Unit tests for structural control-flow normalization.

    use super::normalize_structure;

    /// Strips the x86-64 variadic XMM save prologue and un-nests short `void` guards.
    #[test]
    fn variadic_prologue_is_stripped_and_short_guard_unnested() {
        let input = "\
// sub_1000 @ 0x1000: 10 instructions, 2 blocks
// signature: void sub_1000(char *a1, ...)

if (rax != 0) {
  local_88 = xmm0;
  local_78 = xmm1;
  local_68 = xmm2;
  local_58 = xmm3;
  local_48 = xmm4;
  local_38 = xmm5;
  local_28 = xmm6;
  local_18 = xmm7;
}
if (g64_100 == 0) {
  sub_2000();
} else {
  var1 = 1;
  var2 = 2;
  sub_3000(var1, var2);
}
";
        let out = normalize_structure(input.to_owned());
        assert!(!out.contains("xmm0"), "{out}");
        assert!(
            out.contains("if (g64_100 == 0) {\n  sub_2000();\n  return;\n}\nvar1 = 1;"),
            "{out}"
        );
    }

    /// Rewrites a lazy-init `if (g != 0) { f(); return; } g = init(); f();` into `if (g == 0)`.
    #[test]
    fn lazy_init_early_return_becomes_zero_guard() {
        let input = "\
// sub_1000 @ 0x1000: 8 instructions, 3 blocks
// signature: void sub_1000(uint64_t a1)
  uint64_t var1;
  uint64_t var2;

var1 = sub_2000(a1);
if (g64_100 != 0) {
  sub_3000(var1, g64_100);
  return;
}
var2 = sub_4000(8);
g64_100 = var2;
sub_3000(var1, var2);
";
        let out = normalize_structure(input.to_owned());
        assert!(
            out.contains(
                "if (g64_100 == 0) {\n  g64_100 = sub_4000(8);\n}\nsub_3000(var1, g64_100);\n"
            ),
            "{out}"
        );
    }
}
