use std::cell::RefCell;

thread_local! {
    static DEFINES: RefCell<Defines> = Default::default();
}

#[derive(Default)]
pub struct Defines(Vec<String>);

impl Defines {
    pub fn new(defines: Vec<String>) -> Self {
        Self(defines)
    }
    pub fn contains(&self, ident: &syn::Ident) -> bool {
        self.0.iter().any(|def| ident == def)
    }

    pub fn with_explicit_defines<R>(self, f: impl FnOnce(&Defines) -> R) -> R {
        DEFINES.set(self);
        let ret = Self::with_current_defines(f);
        let _ = DEFINES.take();
        ret
    }

    pub(crate) fn with_current_defines<R>(f: impl FnOnce(&Defines) -> R) -> R {
        DEFINES.with_borrow(f)
    }
}
