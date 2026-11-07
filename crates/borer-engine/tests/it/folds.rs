//! The jump fold's rules over the structurer's text.
//!
//! Each test pins the whole text a rule leaves, where it moved or copied
//! code, so a run that lands on the wrong path fails as surely as a `goto`
//! left behind.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::cleanup;

/// A `switch` whose `default` skips the tail its cases share takes the tail
/// into each case.
///
/// GCC writes a chain of `if (x == k) { v = c; } else if ...` followed by
/// `sink(v);` as compare trees ending in `switch`es whose cases set `v` and
/// break to the shared `sink(v); return;`, while the values no case takes
/// go on to the next chain, too long to copy (here a loop). Each case then
/// ends in the tail, and its `default` falls out of the `switch` to the
/// next chain, with no `goto`.
#[test]
fn a_switch_default_past_the_shared_tail_takes_the_tail_into_each_case() {
    let text = concat!(
        "if (a1 > 0x94a) {\n",
        "  if (a1 > 0xdea) {\n",
        "    switch (a1) {\n",
        "    case 3563: {\n",
        "      var1 = 1;\n",
        "      break;\n",
        "    }\n",
        "    default: goto L_10;\n",
        "    }\n",
        "  } else {\n",
        "    switch (a1) {\n",
        "    case 2379: {\n",
        "      var1 = 2;\n",
        "      break;\n",
        "    }\n",
        "    default: goto L_10;\n",
        "    }\n",
        "  }\n",
        "  sink_i(var1);\n",
        "  return;\n",
        "}\n",
        "L_10:\n",
        "sink_i(3);\n",
        "L_20:\n",
        "sink_i(4);\n",
        "if (a1 == 7) goto L_20;\n",
        "return;\n",
    );
    let want = concat!(
        "if (a1 > 0x94a) {\n",
        "  if (a1 > 0xdea) {\n",
        "    switch (a1) {\n",
        "    case 3563: {\n",
        "      var1 = 1;\n",
        "      sink_i(var1);\n",
        "      return;\n",
        "    }\n",
        "    default: break;\n",
        "    }\n",
        "  } else {\n",
        "    switch (a1) {\n",
        "    case 2379: {\n",
        "      var1 = 2;\n",
        "      sink_i(var1);\n",
        "      return;\n",
        "    }\n",
        "    default: break;\n",
        "    }\n",
        "  }\n",
        "}\n",
        "sink_i(3);\n",
        "do {\n",
        "  sink_i(4);\n",
        "} while (a1 == 7);\n",
        "return;\n",
    );
    assert_eq!(cleanup(text), want);
}

/// A `switch` no arm leaves but by a jump ends its arm of an `if`.
///
/// Every value either returns or jumps past `f(a1)`, so the run before the
/// label belongs only to the missing `else`, not after the `switch`, where
/// it would read as code the cases fall into and keep their jump.
#[test]
fn a_switch_nothing_falls_out_of_ends_its_arm() {
    let text = concat!(
        "if (a1 > 5) {\n",
        "  switch (a1) {\n",
        "  case 6: return 1;\n",
        "  default: goto L_10;\n",
        "  }\n",
        "}\n",
        "f(a1);\n",
        "L_10:\n",
        "g(a1);\n",
        "L_20:\n",
        "h(a1);\n",
        "if (a1 == 7) goto L_20;\n",
        "return 0;\n",
    );
    let want = concat!(
        "if (a1 > 5) {\n",
        "  switch (a1) {\n",
        "  case 6: return 1;\n",
        "  default: break;\n",
        "  }\n",
        "} else {\n",
        "  f(a1);\n",
        "}\n",
        "g(a1);\n",
        "do {\n",
        "  h(a1);\n",
        "} while (a1 == 7);\n",
        "return 0;\n",
    );
    assert_eq!(cleanup(text), want);
}

/// A chain nested once a test, the rest in each `if` and the value's code
/// in its `else`, reads as the `else if` ladder it was written as.
///
/// That is the shape `-O0` code for `if (k == 11) f(1); else if (k == 48)
/// ...` leaves: each test jumps on to the next when it fails. The last
/// test, whose `if` holds no `if`, keeps its arms.
#[test]
fn a_chain_nested_in_its_ifs_reads_as_an_else_if_ladder() {
    let text = concat!(
        "if (a1 != 11) {\n",
        "  if (a1 != 48) {\n",
        "    if (a1 != 85) {\n",
        "      f(4);\n",
        "    } else {\n",
        "      f(3);\n",
        "    }\n",
        "  } else {\n",
        "    f(2);\n",
        "  }\n",
        "} else {\n",
        "  f(1);\n",
        "}\n",
        "return;\n",
    );
    let want = concat!(
        "if (a1 == 11) {\n",
        "  f(1);\n",
        "} else if (a1 == 48) {\n",
        "  f(2);\n",
        "} else if (a1 != 85) {\n",
        "  f(4);\n",
        "} else {\n",
        "  f(3);\n",
        "}\n",
        "return;\n",
    );
    assert_eq!(cleanup(text), want);
}
