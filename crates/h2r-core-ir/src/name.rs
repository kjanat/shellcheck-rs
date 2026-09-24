use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use serde::{Deserialize, Deserializer};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Name(Arc<str>);

thread_local! {
    static INTERNED: RefCell<HashSet<Arc<str>>> = RefCell::new(HashSet::new());
}

impl Name {
    pub fn new(text: &str) -> Name {
        INTERNED.with(|interned| {
            let mut interned = interned.borrow_mut();
            if let Some(shared) = interned.get(text) {
                return Name(shared.clone());
            }
            let shared: Arc<str> = Arc::from(text);
            interned.insert(shared.clone());
            Name(shared)
        })
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Deref for Name {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.0, f)
    }
}

impl From<&str> for Name {
    fn from(text: &str) -> Name {
        Name::new(text)
    }
}

impl From<String> for Name {
    fn from(text: String) -> Name {
        Name::new(&text)
    }
}

impl From<&String> for Name {
    fn from(text: &String) -> Name {
        Name::new(text)
    }
}

impl From<Name> for String {
    fn from(name: Name) -> String {
        name.0.to_string()
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool {
        &*self.0 == other
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        &*self.0 == *other
    }
}

impl PartialEq<String> for Name {
    fn eq(&self, other: &String) -> bool {
        *self.0 == **other
    }
}

impl PartialEq<Name> for str {
    fn eq(&self, other: &Name) -> bool {
        self == &*other.0
    }
}

impl PartialEq<Name> for &str {
    fn eq(&self, other: &Name) -> bool {
        *self == &*other.0
    }
}

impl PartialEq<Name> for String {
    fn eq(&self, other: &Name) -> bool {
        **self == *other.0
    }
}

impl<'de> Deserialize<'de> for Name {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Name, D::Error> {
        let text = <std::borrow::Cow<'de, str>>::deserialize(deserializer)?;
        Ok(Name::new(&text))
    }
}
