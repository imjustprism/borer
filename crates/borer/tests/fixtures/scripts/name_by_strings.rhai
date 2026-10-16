// Names each unnamed function after the one qualified name it references.
//
// Programs built with asserts, logging or tracing often pass the name of
// the function they are in as a string ("Inventory::AddItem failed", a
// __FUNCTION__ argument). A function borer left as sub_ that references
// exactly one string shaped like `Namespace::Name`, and that no other
// unnamed function references, is proposed that name.
//
//   borer script app.exe name_by_strings.rhai --save names.json
//   borer export-pack app.exe mine names.json > mine.borer

fn name_char(c) {
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
        || c == '_' || c == '~'
}

fn qualified(text) {
    let word = text.split(' ')[0];
    word.trim();
    if word.ends_with(":") { word.pop(); }
    if word.ends_with("()") { word.truncate(word.len - 2); }
    let parts = word.split("::");
    if parts.len < 2 { return (); }
    for p in parts {
        if p.len == 0 { return (); }
        for c in p.chars() {
            if !name_char(c) { return (); }
        }
    }
    word
}

let claims = #{};
for f in functions() {
    if !f.name.starts_with("sub_") { continue; }
    let found = [];
    for s in strings(f.entry) {
        let q = qualified(s.text);
        if q != () && !found.contains(q) { found.push(q); }
    }
    if found.len == 1 {
        let q = found[0];
        if q in claims { claims[q].push(f.entry); } else { claims[q] = [f.entry]; }
    }
}

let named = 0;
for q in claims.keys() {
    let entries = claims[q];
    if entries.len == 1 {
        rename(entries[0], q);
        named += 1;
    }
}
print(`named ${named} functions by the one qualified name each references`);
