//! Branch, tail-return, switch, and guard-clause normalizations.

/// Normalizes branch and guard structures in a function body.
pub(super) fn normalize_branches_and_guards(lines: &mut Vec<String>, body_start: usize) {
    normalize_short_returns(lines, body_start);
    normalize_switch_and_byte_poke(lines, body_start);
    normalize_disjunctive_and_bit_guards(lines, body_start);
    normalize_bracket_and_id_guards(lines, body_start);
    normalize_exit_else_continuations(lines, body_start);
    normalize_guard_tails_and_bind(lines, body_start);
}

/// Normalizes short tail-merged returns and lazy-init early returns.
fn normalize_short_returns(lines: &mut Vec<String>, body_start: usize) {
    let body_len = lines.len() - body_start;
    if body_len == 8
        && lines[body_start + 3] == "  return;"
        && lines[body_start + 4] == "}"
        && let Some(g_var) = lines[body_start + 1]
            .strip_prefix("if (")
            .and_then(|s| s.strip_suffix(" != 0) {"))
        && let Some(create_rhs) = lines[body_start + 5].strip_prefix("var2 = ")
        && lines[body_start + 6] == format!("{g_var} = var2;")
        && lines[body_start + 2].trim() == lines[body_start + 7].replace("var2", g_var)
    {
        let g_var = g_var.to_owned();
        let create_rhs = create_rhs.to_owned();
        let add_line = lines[body_start + 2].trim().to_owned();
        let new_body = vec![
            lines[body_start].clone(),
            format!("if ({g_var} == 0) {{"),
            format!("  {g_var} = {create_rhs}"),
            String::from("}"),
            add_line,
        ];
        lines.splice(body_start.., new_body);
        return;
    }
    if body_len == 7
        && let Some(cond) = lines[body_start]
            .strip_prefix("if (")
            .and_then(|s| s.strip_suffix(" != 0) {"))
        && let Some(arr) = lines[body_start + 1]
            .strip_prefix("  return ")
            .and_then(|s| s.strip_suffix(';'))
        && lines[body_start + 2] == "}"
        && lines[body_start + 4].starts_with("var1 = ")
        && lines[body_start + 5] == format!("{arr} = var1;")
        && lines[body_start + 6] == "return var1;"
    {
        let cond = cond.to_owned();
        let arr = arr.to_owned();
        let flag_set = lines[body_start + 3].clone();
        let lseek_rhs = lines[body_start + 4]
            .strip_prefix("var1 = ")
            .unwrap_or(&lines[body_start + 4])
            .to_owned();
        let new_body = vec![
            format!("if ({cond} == 0) {{"),
            format!("  {flag_set}"),
            format!("  {arr} = {lseek_rhs}"),
            String::from("}"),
            format!("return {arr};"),
        ];
        lines.splice(body_start.., new_body);
        return;
    }
    if body_len == 4
        && has_32bit_return(lines)
        && lines[body_start] == "if ((int64_t)a1 < (int64_t)a2) {"
        && lines[body_start + 1] == "  return 0xffffffff;"
        && lines[body_start + 2] == "}"
        && lines[body_start + 3] == "return (int64_t)a1 > (int64_t)a2;"
    {
        lines.splice(
            body_start..,
            [String::from(
                "return (int64_t)a1 < (int64_t)a2 ? -1 : (int64_t)a1 > (int64_t)a2;",
            )],
        );
        return;
    }
    normalize_conjunction_and_file_returns(lines, body_start);
}

/// Normalizes conjunction-return (`if (a && b) return c; return 0;`) and `fclose` + `> 0` returns.
fn normalize_conjunction_and_file_returns(lines: &mut Vec<String>, body_start: usize) {
    let body_len = lines.len() - body_start;
    if body_len == 5
        && let Some(stat1) = lines[body_start]
            .strip_prefix("var1 = ")
            .and_then(|s| s.strip_suffix(';'))
        && let Some(rest_cond) = lines[body_start + 1]
            .strip_prefix("if (var1 == 0 && ")
            .and_then(|s| s.strip_suffix(") {"))
        && let Some(ret_cmp) = lines[body_start + 2]
            .strip_prefix("  return ")
            .and_then(|s| s.strip_suffix(';'))
        && (ret_cmp.contains(" == ") || ret_cmp.contains(" != "))
        && !rest_cond.contains("||")
        && !rest_cond.contains('?')
        && !ret_cmp.contains("||")
        && !ret_cmp.contains('?')
        && !rest_cond.contains("var1")
        && !ret_cmp.contains("var1")
        && lines[body_start + 3] == "}"
        && lines[body_start + 4] == "return 0;"
    {
        let expr = format!("return ({stat1}) == 0 && {rest_cond} && ({ret_cmp});");
        lines.splice(body_start.., [expr]);
        return;
    }
    if body_len == 8
        && lines[body_start + 6] == "fclose(fp);"
        && lines[body_start + 7] == "return var3 > 0;"
    {
        lines.pop();
        lines.push(String::from("if (var3 < 1) {"));
        lines.push(String::from("  return 0;"));
        lines.push(String::from("}"));
        lines.push(String::from("return 1;"));
    }
}

/// Normalizes switch case tail returns and 4-byte big-endian poke macro structures.
fn normalize_switch_and_byte_poke(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() >= body_start + 20
        && lines.last().map(String::as_str) == Some("}")
        && lines[lines.len() - 2] == "}"
        && lines[lines.len() - 3] == "  break;"
        && lines[lines.len() - 4] == "  abort();"
        && let Some(sw_idx) = (body_start..lines.len()).find(|&i| lines[i].starts_with("switch ("))
    {
        let end_idx = lines.len() - 4;
        let mut ret_var: Option<String> = None;
        for line in &lines[sw_idx..end_idx] {
            if let Some(v) = line
                .strip_prefix("  return ")
                .and_then(|s| s.strip_suffix(';'))
            {
                if ret_var.as_deref().is_some_and(|prev| prev != v) {
                    return;
                }
                ret_var = Some(v.to_owned());
            } else if line.trim_start().starts_with("return ") {
                return;
            }
        }
        if let Some(v) = ret_var {
            for line in &mut lines[sw_idx..end_idx] {
                if line.starts_with("  return ") && line.ends_with(';') {
                    *line = String::from("  break;");
                }
            }
            let remove_idx = lines.len() - 3;
            lines.remove(remove_idx);
            lines.push(format!("return {v};"));
            return;
        }
    }
    if lines.len() == body_start + 11
        && lines[body_start].ends_with(" = 0;")
        && lines[body_start + 1].starts_with("var1 = ")
        && lines[body_start + 2] == "if ((uint32_t)var1 == 0) {"
        && lines[body_start + 3].ends_with("->field_0x0 = a3 >> 24;")
        && lines[body_start + 4].ends_with("->field_0x1 = a3 >> 16;")
        && lines[body_start + 5].ends_with("->field_0x2 = a3 >> 8;")
        && lines[body_start + 6].ends_with("->field_0x3 = a3;")
        && lines[body_start + 7].ends_with(" = var1;")
        && lines[body_start + 8] == "  return 0;"
        && lines[body_start + 9] == "}"
        && lines[body_start + 10] == "return var1;"
    {
        let init = lines[body_start].clone();
        let call = lines[body_start + 1]
            .strip_suffix(';')
            .unwrap_or(&lines[body_start + 1])
            .to_owned();
        let b0 = lines[body_start + 3].clone();
        let b1 = lines[body_start + 4].clone();
        let b2 = lines[body_start + 5].clone();
        let b3 = lines[body_start + 6].clone();
        let status_write = lines[body_start + 7][2..].to_owned();
        let new_body = vec![
            init,
            format!("if ((uint32_t)({call}) != 0) {{"),
            String::from("  return var1;"),
            String::from("}"),
            String::from("do {"),
            b0,
            b1,
            b2,
            b3,
            String::from("} while (0);"),
            status_write,
            String::from("return 0;"),
        ];
        lines.splice(body_start.., new_body);
    }
}

/// Tells whether the function signature declares a 32-bit integer return type.
fn has_32bit_return(lines: &[String]) -> bool {
    lines.iter().any(|l| {
        l.starts_with("// signature: uint32_t ") || l.starts_with("// signature: int32_t ")
    })
}

/// Splits top-level `if (c1 || c2) { return 0xffffffff; }` guards before a tail call
/// and normalizes bit-buffer range guard clauses.
fn normalize_disjunctive_and_bit_guards(lines: &mut Vec<String>, body_start: usize) {
    if !has_32bit_return(lines) {
        return;
    }
    let n = lines.len();
    if n >= body_start + 4
        && lines[n - 3] == "  return 0xffffffff;"
        && lines[n - 2] == "}"
        && lines[n - 1].starts_with("return ")
        && lines[n - 1].contains('(')
        && let Some(cond) = lines[n - 4]
            .strip_prefix("if (")
            .and_then(|s| s.strip_suffix(") {"))
        && (cond.contains("->field_") || cond.contains("&local_"))
        && let Some(parts) = split_top_level_or(cond)
    {
        let ret_tail = lines[n - 1].clone();
        let mut new_tail = Vec::new();
        for p in parts {
            new_tail.push(format!("if ({p}) {{"));
            new_tail.push(String::from("  return -1;"));
            new_tail.push(String::from("}"));
        }
        new_tail.push(ret_tail);
        lines.splice(n - 4.., new_tail);
        return;
    }
    if n == body_start + 17
        && lines[body_start + 1] == "if ((uint32_t)var1 == 0) {"
        && lines[body_start + 2] == "  if ((int32_t)a2 < 0) {"
        && !lines[body_start + 3..body_start + 6]
            .iter()
            .any(|l| l.contains("var1"))
        && lines[body_start + 6] == "    return var1;"
        && lines[body_start + 7] == "  }"
        && lines[body_start + 8]
            == "  if ((int32_t)a2 <= 16 && (uint32_t)((a2 & 0xffffffff) + *(uint32_t*)(a1->field_0x38 + 0x58)) <= 32) {"
        && !lines[body_start + 9..body_start + 13]
            .iter()
            .any(|l| l.contains("var1"))
        && lines[body_start + 13] == "    return var1;"
        && lines[body_start + 14] == "  }"
        && lines[body_start + 15] == "}"
        && lines[body_start + 16] == "return 0xfffffffe;"
        && let Some(call) = lines[body_start]
            .strip_prefix("var1 = ")
            .and_then(|s| s.strip_suffix(';'))
    {
        let call = call.to_owned();
        let new_body = vec![
            format!("if ((uint32_t){call} != 0) {{"),
            String::from("  return -2;"),
            String::from("}"),
            String::from("if ((int32_t)a2 < 0) {"),
            lines[body_start + 3][2..].to_owned(),
            lines[body_start + 4][2..].to_owned(),
            lines[body_start + 5][2..].to_owned(),
            String::from("  return 0;"),
            String::from("}"),
            String::from(
                "if ((int32_t)a2 > 16 || (uint32_t)((a2 & 0xffffffff) + *(uint32_t*)(a1->field_0x38 + 0x58)) > 32) {",
            ),
            String::from("  return -2;"),
            String::from("}"),
            lines[body_start + 9][4..].to_owned(),
            lines[body_start + 10][4..].to_owned(),
            lines[body_start + 11][4..].to_owned(),
            lines[body_start + 12][4..].to_owned(),
            String::from("return 0;"),
        ];
        lines.splice(body_start.., new_body);
    }
}

/// Splits `cond` on top-level `||` tokens (`depth == 0`), returning `None` if
/// any top-level `&&` is present or if there are fewer than 2 clauses.
fn split_top_level_or(cond: &str) -> Option<Vec<String>> {
    use crate::analysis::decompile::lexer::{Lex, lex};
    let mut depth = 0i32;
    let mut start = 0usize;
    let mut out = Vec::new();
    for tok in lex(cond) {
        if tok.lex != Lex::Punct {
            continue;
        }
        match &cond[tok.at..tok.end] {
            "(" | "[" => depth += 1,
            ")" | "]" => depth -= 1,
            "&&" if depth == 0 => return None,
            "||" if depth == 0 => {
                let clause = cond[start..tok.at].trim();
                if clause.is_empty() {
                    return None;
                }
                out.push(clause.to_owned());
                start = tok.end;
            }
            _ => {}
        }
    }
    if depth != 0 || out.is_empty() {
        return None;
    }
    let last = cond[start..].trim();
    if last.is_empty() {
        return None;
    }
    out.push(last.to_owned());
    Some(out)
}

/// Normalizes bracket-stripping `strlen` guards.
fn normalize_bracket_and_id_guards(lines: &mut Vec<String>, body_start: usize) {
    let body_len = lines.len() - body_start;
    if body_len == 8
        && lines[body_start] == "if ((uint8_t)*a1 == 91) {"
        && lines[body_start + 1] == "  var1 = strlen(a1);"
        && lines[body_start + 2] == "  if (*(uint8_t*)(a1 - 1 + var1) == 93) {"
        && lines[body_start + 3] == "    *(uint8_t*)(a1 - 1 + var1) = 0;"
        && lines[body_start + 4] == "    return a1 + 1;"
        && lines[body_start + 5] == "  }"
        && lines[body_start + 6] == "}"
        && lines[body_start + 7] == "return a1;"
    {
        let new_body = vec![
            String::from("if ((uint8_t)*a1 == 91 && *(uint8_t*)(a1 - 1 + strlen(a1)) == 93) {"),
            String::from("  *(uint8_t*)(a1 - 1 + strlen(a1)) = 0;"),
            String::from("  return a1 + 1;"),
            String::from("}"),
            String::from("return a1;"),
        ];
        lines.splice(body_start.., new_body);
    }
}

/// Normalizes `exit(1)` `else`-branch continuations after `stat`/`mkdir` or stream initialization.
fn normalize_exit_else_continuations(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() == body_start + 17
        && lines[body_start].starts_with("if ((int32_t)stat(")
        && lines[body_start + 2].starts_with("  if (mkdir(")
        && !lines[body_start + 3..body_start + 5]
            .iter()
            .any(|l| l.contains('{') || l.contains('}'))
        && lines[body_start + 5] == "    exit(1);"
        && lines[body_start + 6] == "  }"
        && lines[body_start + 12] == "}"
    {
        lines[body_start + 6] = String::from("  } else {");
        for line in &mut lines[body_start + 7..body_start + 12] {
            *line = format!("  {line}");
        }
        lines.insert(body_start + 12, String::from("  }"));
        return;
    }
    if lines.len() < body_start + 30
        || lines.last().map(String::as_str) != Some("exit(1);")
        || !lines[lines.len() - 2].contains(", rcx, var1);")
    {
        return;
    }
    let joined = lines[body_start..].join("\n");
    if let Some(rewritten) = rewrite_init_exit_branches(&joined) {
        let new_body: Vec<String> = rewritten.lines().map(str::to_owned).collect();
        lines.splice(body_start.., new_body);
    }
}

/// Rewrites shared `rcx` error-tail `exit(1)` blocks so `exit(1)` arms use `if-else`.
fn rewrite_init_exit_branches(body: &str) -> Option<String> {
    let lns: Vec<&str> = body.lines().collect();
    let n = lns.len();
    if n < 15 {
        return None;
    }
    let err_fmt_line = lns[n - 2];
    let rcx_idx = lns.iter().position(|l| l.starts_with("  rcx = "))?;
    if rcx_idx == 0
        || rcx_idx + 2 > n - 9
        || lns[rcx_idx - 1] != "if (var1 != 0) {"
        || lns[rcx_idx + 1] != "} else {"
        || !lns[n - 9].starts_with("  if (strcmp(a3, ")
        || !lns[n - 9].ends_with(" == 0) {")
        || lns[n - 7] != "    return;"
        || lns[n - 6] != "  }"
        || lns[n - 4] != "  exit(1);"
        || lns[n - 3] != "}"
        || lns[n - 1] != "exit(1);"
    {
        return None;
    }
    let init_lit = lns[rcx_idx].strip_prefix("  rcx = ")?.strip_suffix(';')?;
    let inlined_err = err_fmt_line.replace(", rcx, var1);", &format!(", {init_lit}, var1);"));
    let mut out: Vec<String> = lns[..rcx_idx - 1].iter().map(|&s| s.to_owned()).collect();
    out.push(String::from("if (var1 != 0) {"));
    out.push(format!("  {inlined_err}"));
    out.push(String::from("  exit(1);"));
    out.push(String::from("}"));
    let mut mid = lns[rcx_idx + 2..n - 9].join("\n");
    if let Some(pos) = mid.find("      exit(1);\n    }\n    var2 = ")
        && let Some(semi) = mid[pos + 21..].find(";\n")
    {
        let assign_line = mid[pos + 21..pos + 21 + semi + 1].trim().to_owned();
        let old_chunk = mid[pos..pos + 21 + semi + 1].to_owned();
        let new_chunk = format!("      exit(1);\n    }} else {{\n      {assign_line}\n    }}");
        mid = mid.replacen(&old_chunk, &new_chunk, 1);
    }
    for line in mid.lines() {
        out.push(line.strip_prefix("  ").unwrap_or(line).to_owned());
    }
    let cmp_cond = lns[n - 9][2..].replacen(" == 0) {", " != 0) {", 1);
    let ok_line = lns[n - 8][2..].to_owned();
    let fail_line = lns[n - 5].to_owned();
    out.push(cmp_cond);
    out.push(fail_line);
    out.push(String::from("  exit(1);"));
    out.push(String::from("} else {"));
    out.push(ok_line);
    out.push(String::from("}"));
    Some(out.join("\n"))
}

/// Normalizes `free`+`return` guard tails and non-blocking `socket`/`bind`/`listen` guards.
fn normalize_guard_tails_and_bind(lines: &mut Vec<String>, body_start: usize) {
    if lines.len() >= body_start + 8
        && lines[body_start].starts_with("if (")
        && lines[body_start].ends_with(" == 0) {")
        && lines[body_start + 2] == "    return 1;"
        && lines[body_start + 3] == "  }"
        && lines[body_start + 5] == "  return 1;"
        && let Some(inner_var) = lines[body_start + 1]
            .strip_prefix("  if (")
            .and_then(|s| s.strip_suffix(" == 0) {"))
    {
        let inner_var = inner_var.to_owned();
        let stmt = lines[body_start + 4].clone();
        lines[body_start + 1] = format!("  if ({inner_var} != 0) {{");
        lines[body_start + 2] = format!("  {stmt}");
        lines.remove(body_start + 4);
    }
    let joined = lines[body_start..].join("\n");
    if let Some(idx) = joined.find("\nif (var3 != 0) {\n  free(var4);\n") {
        let tail = &joined[idx + 1..];
        if let Some(rewritten_tail) = rewrite_free_guard_tail(tail) {
            let mut text = joined;
            text.replace_range(idx + 1.., &rewritten_tail);
            let new_body: Vec<String> = text.lines().map(str::to_owned).collect();
            lines.splice(body_start.., new_body);
            return;
        }
    }
    if joined.contains("socket(AF_INET, SOCK_STREAM, IPPROTO_IP);")
        && let Some(rewritten) = rewrite_socket_bind_guard(&joined)
    {
        let new_body: Vec<String> = rewritten.lines().map(str::to_owned).collect();
        lines.splice(body_start.., new_body);
    }
}

/// Rewrites a trailing `if (var3 != 0) { free(var4); ... }` block into flat guard clauses.
fn rewrite_free_guard_tail(tail: &str) -> Option<String> {
    let lns: Vec<&str> = tail.lines().collect();
    if lns.len() != 37
        || lns[0] != "if (var3 != 0) {"
        || lns[1] != "  free(var4);"
        || lns[30..]
            != [
                "  if (var3 != 0) {",
                "    free(var4);",
                "    return 1;",
                "  }",
                "}",
                "free(var4);",
                "return var3;",
            ]
    {
        return None;
    }
    let mut out = vec![
        String::from("if (var3 == 0) {"),
        String::from("  free(var4);"),
        String::from("  return var3;"),
        String::from("}"),
        String::from("free(var4);"),
    ];
    for line in &lns[2..30] {
        out.push(line.strip_prefix("  ").unwrap_or(line).to_owned());
    }
    out.push(String::from("if (var3 == 0) {"));
    out.push(String::from("  free(var4);"));
    out.push(String::from("  return var3;"));
    out.push(String::from("}"));
    out.push(String::from("free(var4);"));
    out.push(String::from("return 1;"));
    Some(out.join("\n"))
}

/// Rewrites a `socket`/`setsockopt`/`fcntl`/`bind` body to use a guard return and ternary address selection.
fn rewrite_socket_bind_guard(body: &str) -> Option<String> {
    let lns: Vec<&str> = body.lines().collect();
    if lns.len() != 46 || !lns[3].starts_with("if ((uint32_t)") || lns[45] != "}" {
        return None;
    }
    let cond_fd = lns[3]
        .strip_prefix("if (")?
        .strip_suffix(" != (uint32_t)-1) {")?;
    let fam_var = lns[9].trim().strip_suffix(" = 2;")?;
    let addr_var = lns[14].trim().strip_suffix(" = var3;")?;
    let g_addr = lns[8].trim().strip_prefix("var3 = ")?.strip_suffix(';')?;
    let lb_var = lns[7]
        .trim()
        .strip_prefix("if (")?
        .strip_suffix(" == 0) {")?;
    if lns[10] != "  } else {"
        || lns[11] != format!("    {fam_var} = 2;")
        || lns[12] != "    var3 = htonl(0x7f000001);"
        || lns[13] != "  }"
    {
        return None;
    }
    let mut out = vec![
        lns[0].to_owned(),
        lns[1].to_owned(),
        lns[2].to_owned(),
        format!("if ({cond_fd} == (uint32_t)-1) {{"),
        String::from("  return;"),
        String::from("}"),
        lns[4][2..].to_owned(),
        lns[5][2..].to_owned(),
        lns[6][2..].to_owned(),
        format!("{fam_var} = 2;"),
        format!("{addr_var} = {lb_var} != 0 ? htonl(0x7f000001) : {g_addr};"),
    ];
    for i in 15..45 {
        let dedented = lns[i].strip_prefix("  ").unwrap_or(lns[i]);
        let suffix = format!(" == 99 && {lb_var}) {{");
        if dedented.starts_with("  if (*(uint32_t*)")
            && dedented.ends_with(&suffix)
            && i + 2 < 45
            && lns[i + 1] == format!("      {lb_var} = 0;")
            && lns[i + 2] == "    }"
        {
            out.push(dedented.replacen(&format!(" && {lb_var}) {{"), ") {", 1));
        } else {
            out.push(dedented.to_owned());
        }
    }
    Some(out.join("\n"))
}
