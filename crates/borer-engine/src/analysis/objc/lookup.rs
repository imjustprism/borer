//! The implementation a message reaches, as the image's metadata shows it
//! ([`Index::reach`]).

use std::collections::{BTreeMap, BTreeSet};

use super::{Arg, ObjcCategory, ObjcClass, ObjcFacts, ObjcMethod};

/// Most superclasses a lookup walks, against a cycle a hostile image writes.
const DEPTH_MAX: usize = 64;

/// Most subclasses one override check visits; past it the message may be
/// overridden.
const SUBCLASSES_MAX: usize = 4096;

/// Most subclasses all the override checks of one image visit together;
/// past it every message left may be overridden.
const VISITS_MAX: usize = 1 << 20;

/// What a message's receiver is known to be.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Receiver {
    /// A class object, whose class methods take the message: `exact` for
    /// the class a class reference names, else it or a subclass (`self` in
    /// a class method).
    Class {
        /// The class.
        name: String,
        /// Whether the class object is that class's and no subclass's.
        exact: bool,
    },
    /// An instance: `exact` for what `alloc` makes, else one of the class
    /// or of a subclass (`self` in an instance method).
    Instance {
        /// The class.
        name: String,
        /// Whether the instance is of that class and no subclass.
        exact: bool,
    },
    /// `super` in a method of `class`: the lookup starts at its superclass.
    Super {
        /// The class whose method sends it.
        class: String,
        /// Whether that method is a class method.
        class_method: bool,
    },
    /// Nothing the metadata shows.
    Unknown,
}

impl Receiver {
    /// Reads what a send's receiver argument is.
    ///
    /// # Arguments
    ///
    /// * `arg` - Where the receiver argument got its value; `None` for a
    ///   super send.
    /// * `method` - The class of the method that sends it and whether that
    ///   is a class method, when the sender is one.
    /// * `facts` - The metadata, for the class references.
    /// * `results` - What each earlier send's result is, by its call site.
    pub(crate) fn of(
        arg: Option<Arg>,
        method: Option<(&str, bool)>,
        facts: &ObjcFacts,
        results: &BTreeMap<u64, Receiver>,
    ) -> Receiver {
        match arg {
            None => method.map_or(Receiver::Unknown, |(class, class_method)| Receiver::Super {
                class: class.to_owned(),
                class_method,
            }),
            Some(Arg::Slot(slot)) => facts
                .classrefs
                .get(&slot)
                .map_or(Receiver::Unknown, |name| Receiver::Class {
                    name: name.clone(),
                    exact: true,
                }),
            Some(Arg::Result(site)) => results.get(&site).cloned().unwrap_or(Receiver::Unknown),
            Some(Arg::Param(0)) => method.map_or(Receiver::Unknown, |(class, class_method)| {
                let name = class.to_owned();
                if class_method {
                    Receiver::Class { name, exact: false }
                } else {
                    Receiver::Instance { name, exact: false }
                }
            }),
            Some(Arg::Param(_) | Arg::Unknown) => Receiver::Unknown,
        }
    }

    /// Returns what a message to this receiver hands back, as far as its
    /// selector shows.
    ///
    /// `alloc` makes an instance of exactly the class; `new` and an `init`
    /// method hand back one of the class or of a subclass, since an
    /// initializer may return a replacement; `self`, `retain` and
    /// `autorelease` hand the receiver back and `class` an instance's
    /// class. An allocator, `self`, `retain`, `autorelease` or `class` the
    /// image defines may hand back anything.
    ///
    /// # Arguments
    ///
    /// * `selector` - The message's selector.
    /// * `reaches` - The implementation the message reaches in the image,
    ///   `None` when the image defines none.
    pub(crate) fn result_of(&self, selector: &str, reaches: Option<Reach>) -> Receiver {
        let init = selector
            .strip_prefix("init")
            .is_some_and(|rest| !rest.starts_with(|c: char| c.is_ascii_lowercase()));
        let own = reaches.is_some();
        match self {
            Receiver::Class { name, exact }
                if !own && matches!(selector, "alloc" | "new" | "allocWithZone:") =>
            {
                Receiver::Instance {
                    name: name.clone(),
                    exact: *exact && selector != "new",
                }
            }
            Receiver::Instance { name, .. } if init => Receiver::Instance {
                name: name.clone(),
                exact: false,
            },
            Receiver::Instance { .. }
                if !own && matches!(selector, "self" | "retain" | "autorelease") =>
            {
                self.clone()
            }
            Receiver::Instance { name, exact } if !own && selector == "class" => Receiver::Class {
                name: name.clone(),
                exact: *exact,
            },
            Receiver::Class { .. }
            | Receiver::Instance { .. }
            | Receiver::Super { .. }
            | Receiver::Unknown => Receiver::Unknown,
        }
    }
}

/// The implementation a message reaches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reach {
    /// The implementation's entry.
    pub imp: u64,
    /// Whether nothing else in the image can take the message: no subclass
    /// the receiver may be overrides it and no second category defines it.
    pub sure: bool,
}

/// The image's classes and categories by name, read once for every lookup.
pub(crate) struct Index<'f> {
    /// Each class the image defines, by name.
    classes: BTreeMap<&'f str, &'f ObjcClass>,
    /// The categories on each class, by the class's name.
    categories: BTreeMap<&'f str, Vec<&'f ObjcCategory>>,
    /// The classes each class is the superclass of, by its name.
    children: BTreeMap<&'f str, Vec<&'f str>>,
    /// The selectors each class and the categories on it define, with
    /// whether each is a class method, by the class's name.
    defined: BTreeMap<&'f str, BTreeSet<(&'f str, bool)>>,
    /// The override answers found so far, by class, selector and kind.
    memo: BTreeMap<(String, String, bool), bool>,
    /// The subclasses the override checks may still visit.
    visits: usize,
}

impl<'f> Index<'f> {
    /// Indexes the classes and categories the metadata describes.
    ///
    /// # Arguments
    ///
    /// * `facts` - The image's Objective-C metadata.
    pub(crate) fn new(facts: &'f ObjcFacts) -> Self {
        let mut index = Index {
            classes: BTreeMap::new(),
            categories: BTreeMap::new(),
            children: BTreeMap::new(),
            defined: BTreeMap::new(),
            memo: BTreeMap::new(),
            visits: VISITS_MAX,
        };
        let mut define = |class: &'f str, methods: &'f [ObjcMethod]| {
            let set = index.defined.entry(class).or_default();
            set.extend(
                methods
                    .iter()
                    .map(|m| (m.selector.as_str(), m.class_method)),
            );
        };
        for c in &facts.classes {
            define(c.name.as_str(), &c.methods);
        }
        for c in &facts.categories {
            define(c.class.as_str(), &c.methods);
        }
        for c in &facts.classes {
            index.classes.entry(c.name.as_str()).or_insert(c);
            if let Some(up) = c.superclass.as_deref() {
                index.children.entry(up).or_default().push(c.name.as_str());
            }
        }
        for c in &facts.categories {
            index
                .categories
                .entry(c.class.as_str())
                .or_default()
                .push(c);
        }
        index
    }

    /// Finds the implementation a message to `receiver` reaches.
    ///
    /// The runtime looks a selector up in the categories on the receiver's
    /// class first, then in the class's own list, then up the superclass
    /// chain; a class method in the metaclass's. A class the image does
    /// not define ends the walk unanswered: its methods are another
    /// image's.
    ///
    /// # Arguments
    ///
    /// * `receiver` - What the receiver is.
    /// * `selector` - The selector.
    ///
    /// # Returns
    ///
    /// The implementation and whether it is sure, or `None` when the
    /// receiver is unknown or no class the image defines has the method.
    pub(crate) fn reach(&mut self, receiver: &Receiver, selector: &str) -> Option<Reach> {
        let (class, class_method, exact) = match receiver {
            Receiver::Class { name, exact } => (name.as_str(), true, *exact),
            Receiver::Instance { name, exact } => (name.as_str(), false, *exact),
            Receiver::Super {
                class,
                class_method,
            } => (
                self.classes.get(class.as_str())?.superclass.as_deref()?,
                *class_method,
                true,
            ),
            Receiver::Unknown => return None,
        };
        let (imp, alone) = self.lookup(class, selector, class_method)?;
        let overridden = !exact && self.overridden(class, selector, class_method);
        Some(Reach {
            imp,
            sure: alone && !overridden,
        })
    }

    /// Walks the lookup from `class` up its superclasses.
    ///
    /// # Arguments
    ///
    /// * `class` - Where the lookup starts.
    /// * `selector` - The selector.
    /// * `class_method` - Whether the metaclass's methods take it.
    ///
    /// # Returns
    ///
    /// The implementation, and whether no second category on the class
    /// that has it defines it too.
    fn lookup(&self, class: &str, selector: &str, class_method: bool) -> Option<(u64, bool)> {
        let mut name = class;
        for _ in 0..DEPTH_MAX {
            let mut found = self
                .categories
                .get(name)
                .into_iter()
                .flatten()
                .filter_map(|c| find(&c.methods, selector, class_method));
            if let Some(imp) = found.next() {
                return Some((imp, found.next().is_none()));
            }
            let c = self.classes.get(name)?;
            if let Some(imp) = find(&c.methods, selector, class_method) {
                return Some((imp, true));
            }
            name = c.superclass.as_deref()?;
        }
        None
    }

    /// Tells whether a subclass of `class` the image defines, or a category
    /// on one, defines the selector, so a receiver that may be one of them
    /// may reach that method instead.
    ///
    /// A hierarchy past [`SUBCLASSES_MAX`], one that reaches a class twice
    /// (it loops, or two classes share a name), or a check once the
    /// image's checks have visited [`VISITS_MAX`] subclasses, may; each
    /// class is walked once, and each answer is kept for the next message
    /// that asks.
    ///
    /// # Arguments
    ///
    /// * `class` - The receiver's class.
    /// * `selector` - The selector.
    /// * `class_method` - Whether the metaclasses' methods take it.
    fn overridden(&mut self, class: &str, selector: &str, class_method: bool) -> bool {
        let key = (class.to_owned(), selector.to_owned(), class_method);
        if let Some(&known) = self.memo.get(&key) {
            return known;
        }
        let mut todo: Vec<&str> = self.children.get(class).cloned().unwrap_or_default();
        let mut walked: BTreeSet<&str> = BTreeSet::new();
        let mut found = false;
        while let Some(name) = todo.pop() {
            if !walked.insert(name) || walked.len() > SUBCLASSES_MAX || self.visits == 0 {
                found = true;
                break;
            }
            self.visits -= 1;
            if self
                .defined
                .get(name)
                .is_some_and(|set| set.contains(&(selector, class_method)))
            {
                found = true;
                break;
            }
            todo.extend(self.children.get(name).into_iter().flatten().copied());
        }
        self.memo.insert(key, found);
        found
    }
}

/// The class each implementation is a method of, by its entry: the class
/// a category extends for a category's method, and whether it is a class
/// method.
///
/// An implementation two classes, or a class and its metaclass, share
/// (one body the linker folded) is left out: its `self` may be either.
///
/// # Arguments
///
/// * `facts` - The metadata.
pub(crate) fn method_classes(facts: &ObjcFacts) -> BTreeMap<u64, (&str, bool)> {
    let mut out: BTreeMap<u64, Option<(&str, bool)>> = BTreeMap::new();
    let lists = facts
        .classes
        .iter()
        .map(|c| (c.name.as_str(), &c.methods))
        .chain(
            facts
                .categories
                .iter()
                .map(|c| (c.class.as_str(), &c.methods)),
        );
    for (class, list) in lists {
        for m in list {
            if let Some(imp) = m.imp {
                let own = Some((class, m.class_method));
                out.entry(imp)
                    .and_modify(|c| {
                        if *c != own {
                            *c = None;
                        }
                    })
                    .or_insert(own);
            }
        }
    }
    out.into_iter()
        .filter_map(|(imp, c)| Some((imp, c?)))
        .collect()
}

/// The implementation a method list gives a selector.
///
/// # Arguments
///
/// * `methods` - The list.
/// * `selector` - The selector.
/// * `class_method` - Whether a class method is looked for.
fn find(methods: &[ObjcMethod], selector: &str, class_method: bool) -> Option<u64> {
    methods
        .iter()
        .find(|m| m.selector == selector && m.class_method == class_method)
        .and_then(|m| m.imp)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::collections::BTreeMap;

    use super::{Index, Reach, Receiver, method_classes};
    use crate::analysis::objc::{Arg, ObjcCategory, ObjcClass, ObjcFacts, ObjcMethod};

    /// A method of the given kind, selector and implementation.
    ///
    /// # Arguments
    ///
    /// * `class_method` - Whether it is a class method.
    /// * `selector` - The selector.
    /// * `imp` - The implementation.
    fn method(class_method: bool, selector: &str, imp: u64) -> ObjcMethod {
        ObjcMethod {
            selector: selector.to_owned(),
            class_method,
            imp: Some(imp),
        }
    }

    /// A class with a superclass and methods.
    ///
    /// # Arguments
    ///
    /// * `name` - The class.
    /// * `superclass` - Its superclass.
    /// * `methods` - Its methods.
    fn class(name: &str, superclass: &str, methods: Vec<ObjcMethod>) -> ObjcClass {
        ObjcClass {
            name: name.to_owned(),
            superclass: Some(superclass.to_owned()),
            address: 0,
            methods,
        }
    }

    /// `Base : NSObject` with `-run` and `+make`, `Sub : Base` overriding
    /// `-run`, `Leaf : Sub` with nothing, and two categories on `Base`
    /// that both define `-extra`.
    fn facts() -> ObjcFacts {
        let category = |name: &str, imp| ObjcCategory {
            name: name.to_owned(),
            class: "Base".to_owned(),
            methods: vec![method(false, "extra", imp)],
        };
        ObjcFacts {
            classes: vec![
                class(
                    "Base",
                    "NSObject",
                    vec![method(false, "run", 0x100), method(true, "make", 0x110)],
                ),
                class("Sub", "Base", vec![method(false, "run", 0x200)]),
                class("Leaf", "Sub", Vec::new()),
            ],
            categories: vec![category("Extra", 0x300), category("Twice", 0x310)],
            ..ObjcFacts::default()
        }
    }

    /// A message reaches the method the runtime's lookup finds.
    ///
    /// The lookup takes the class's own method, then a superclass's, a
    /// category's before either; it is sure where the receiver is exactly
    /// the class, or no subclass the image defines overrides the method,
    /// and where one category alone defines it; once the image's override
    /// checks have spent their visits, a subclass may override it.
    #[test]
    fn a_message_reaches_the_method_the_lookup_finds() {
        let facts = facts();
        let mut index = Index::new(&facts);
        let class = |name: &str, exact| Receiver::Class {
            name: name.to_owned(),
            exact,
        };
        let instance = |name: &str, exact| Receiver::Instance {
            name: name.to_owned(),
            exact,
        };
        let reach = |imp, sure| Some(Reach { imp, sure });
        assert_eq!(
            index.reach(&class("Base", true), "make"),
            reach(0x110, true)
        );
        assert_eq!(
            index.reach(&class("Leaf", true), "make"),
            reach(0x110, true)
        );
        assert_eq!(
            index.reach(&instance("Base", true), "run"),
            reach(0x100, true)
        );
        assert_eq!(
            index.reach(&instance("Base", false), "run"),
            reach(0x100, false)
        );
        assert_eq!(
            index.reach(&instance("Sub", false), "run"),
            reach(0x200, true)
        );
        assert_eq!(
            index.reach(&instance("Leaf", false), "run"),
            reach(0x200, true)
        );
        let sup = Receiver::Super {
            class: "Sub".to_owned(),
            class_method: false,
        };
        assert_eq!(index.reach(&sup, "run"), reach(0x100, true));
        assert_eq!(
            index.reach(&instance("Leaf", true), "extra"),
            reach(0x300, false)
        );
        assert_eq!(index.reach(&instance("Base", true), "make"), None);
        assert_eq!(index.reach(&instance("NSString", true), "run"), None);
        assert_eq!(index.reach(&Receiver::Unknown, "run"), None);
        let mut spent = Index::new(&facts);
        spent.visits = 0;
        assert_eq!(
            spent.reach(&instance("Sub", false), "run"),
            reach(0x200, false)
        );
    }

    /// A message's result keeps what its selector shows of the receiver.
    ///
    /// `alloc` makes an instance of exactly the class, `new` and an `init`
    /// method one of the class or a subclass, `self` the receiver and
    /// `class` an instance's class, each unless the image defines the
    /// allocator or the method (an `init` method aside); `initialize` is no
    /// `init` method and anything else is unknown.
    #[test]
    fn a_message_result_keeps_what_its_selector_shows() {
        let class = Receiver::Class {
            name: "Base".to_owned(),
            exact: true,
        };
        let instance = |exact| Receiver::Instance {
            name: "Base".to_owned(),
            exact,
        };
        let own = Some(Reach {
            imp: 0x100,
            sure: true,
        });
        let exact = class.result_of("alloc", None);
        assert_eq!(exact, instance(true));
        assert_eq!(class.result_of("alloc", own), Receiver::Unknown);
        assert_eq!(class.result_of("new", own), Receiver::Unknown);
        assert_eq!(class.result_of("new", None), instance(false));
        assert_eq!(exact.result_of("initWithName:", None), instance(false));
        assert_eq!(exact.result_of("init", own), instance(false));
        assert_eq!(exact.result_of("self", None), exact);
        assert_eq!(exact.result_of("self", own), Receiver::Unknown);
        assert_eq!(exact.result_of("class", None), class);
        assert_eq!(exact.result_of("class", own), Receiver::Unknown);
        assert_eq!(exact.result_of("initialize", None), Receiver::Unknown);
        assert_eq!(class.result_of("shared", None), Receiver::Unknown);
    }

    /// Only the first argument of a method is `self`; another argument is
    /// nothing the metadata shows.
    #[test]
    fn only_the_first_argument_is_self() {
        let facts = ObjcFacts::default();
        let results = BTreeMap::new();
        let method = Some(("Base", false));
        assert_eq!(
            Receiver::of(Some(Arg::Param(0)), method, &facts, &results),
            Receiver::Instance {
                name: "Base".to_owned(),
                exact: false
            }
        );
        assert_eq!(
            Receiver::of(Some(Arg::Param(2)), method, &facts, &results),
            Receiver::Unknown
        );
        assert_eq!(
            Receiver::of(Some(Arg::Param(0)), None, &facts, &results),
            Receiver::Unknown
        );
    }

    /// An implementation two classes share is no class's method, while one
    /// a class lists twice stays its.
    #[test]
    fn a_shared_implementation_has_no_class() {
        let facts = ObjcFacts {
            classes: vec![
                class(
                    "A",
                    "NSObject",
                    vec![method(false, "yes", 0x100), method(false, "no", 0x200)],
                ),
                class(
                    "B",
                    "NSObject",
                    vec![method(false, "yes", 0x100), method(false, "same", 0x300)],
                ),
            ],
            categories: vec![ObjcCategory {
                name: "More".to_owned(),
                class: "B".to_owned(),
                methods: vec![method(false, "again", 0x300)],
            }],
            ..ObjcFacts::default()
        };
        let own = method_classes(&facts);
        assert_eq!(own.get(&0x100), None);
        assert_eq!(own.get(&0x200), Some(&("A", false)));
        assert_eq!(own.get(&0x300), Some(&("B", false)));
    }

    /// A superclass chain that loops ends the lookup unanswered, and an
    /// override check over it says the message may be overridden once it
    /// reaches a class twice, having walked each class once.
    #[test]
    fn a_looping_hierarchy_ends_the_lookup() {
        let facts = ObjcFacts {
            classes: vec![class("A", "B", Vec::new()), class("B", "A", Vec::new())],
            ..ObjcFacts::default()
        };
        let mut index = Index::new(&facts);
        let a = Receiver::Instance {
            name: "A".to_owned(),
            exact: false,
        };
        assert_eq!(index.reach(&a, "nope"), None);
        assert!(index.overridden("A", "nope", false));
        let wide = ObjcFacts {
            classes: std::iter::once(class("A", "B", Vec::new()))
                .chain((0..1000).map(|i| class(&format!("C{i}"), "A", Vec::new())))
                .chain(std::iter::once(class("B", "A", Vec::new())))
                .collect(),
            ..ObjcFacts::default()
        };
        let mut index = Index::new(&wide);
        assert!(index.overridden("A", "nope", false));
        assert!(
            super::VISITS_MAX - index.visits <= 2,
            "{} visits",
            super::VISITS_MAX - index.visits
        );
    }
}
