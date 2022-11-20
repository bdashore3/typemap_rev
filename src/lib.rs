//! A hashmap whose keys are defined by types.

use std::any::{Any, TypeId};
use std::collections::hash_map::IntoIter;
use std::collections::hash_map::{
    Entry as HashMapEntry, OccupiedEntry as HashMapOccupiedEntry, VacantEntry as HashMapVacantEntry,
};
use std::collections::HashMap;
use std::fmt::Debug;
use std::iter::FromIterator;
use std::marker::PhantomData;

/// The default type used for storing values in a [`TypeMap`].
pub type DefaultStorage = dyn Any + Send + Sync;

/// Storage type that allows cloning a [`TypeMap`] if the values inside it all
/// implement [`Clone`].
pub trait CloneableStorage: Any + Send + Sync {
    #[doc(hidden)]
    fn clone_storage(&self) -> Box<dyn CloneableStorage>;
}

impl<T: Any + Send + Sync + Clone> CloneableStorage for T {
    fn clone_storage(&self) -> Box<dyn CloneableStorage> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn CloneableStorage> {
    fn clone(&self) -> Self {
        (**self).clone_storage()
    }
}

/// Storage type that allows formatting a [`TypeMap`] in debug representation if
/// the values inside it all implement [`Debug`].
pub trait DebuggableStorage: Any + Send + Sync + Debug {}
impl<T: Any + Send + Sync + Debug> DebuggableStorage for T {}

/// Storage type that allows cloning and formatting a [`TypeMap`] in debug representation if
/// the values inside it all implement [`Clone`] *and* [`Debug`].
pub trait CloneDebuggableStorage: DebuggableStorage {
    #[doc(hidden)]
    fn clone_storage(&self) -> Box<dyn CloneDebuggableStorage>;
}

impl<T: DebuggableStorage + Clone> CloneDebuggableStorage for T {
    fn clone_storage(&self) -> Box<dyn CloneDebuggableStorage> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn CloneDebuggableStorage> {
    fn clone(&self) -> Self {
        (**self).clone_storage()
    }
}

#[doc(hidden)]
pub trait IntoBox<T: ?Sized> {
    fn into_box(self) -> Box<T>;
}

impl<T: Any + Send + Sync> IntoBox<(dyn Any + Send + Sync)> for T {
    fn into_box(self) -> Box<dyn Any + Send + Sync> {
        Box::new(self)
    }
}

impl<T: CloneableStorage> IntoBox<dyn CloneableStorage> for T {
    fn into_box(self) -> Box<dyn CloneableStorage> {
        Box::new(self)
    }
}

impl<T: DebuggableStorage> IntoBox<dyn DebuggableStorage> for T {
    fn into_box(self) -> Box<dyn DebuggableStorage> {
        Box::new(self)
    }
}

impl<T: CloneDebuggableStorage> IntoBox<dyn CloneDebuggableStorage> for T {
    fn into_box(self) -> Box<dyn CloneDebuggableStorage> {
        Box::new(self)
    }
}

/// TypeMapKey is used to declare key types that are eligible for use
/// with [`TypeMap`].
///
/// [`TypeMap`]: struct.TypeMap.html
pub trait TypeMapKey: Any {
    /// Defines the value type that corresponds to this `TypeMapKey`.
    type Value: Any + Send + Sync;
}

/// TypeMap is a simple abstraction around the standard library's [`HashMap`]
/// type, where types are its keys. This allows for statically-checked value
/// retrieval.
///
/// [`HashMap`]: std::collections::HashMap
pub struct TypeMap<S: ?Sized = DefaultStorage>(HashMap<TypeId, Box<S>>);

impl TypeMap {
    /// Creates a new instance of `TypeMap`.
    #[inline]
    pub fn new() -> Self {
        Self::custom()
    }
}

impl<S: ?Sized + Any + Send + Sync> TypeMap<S> {
    /// Creates a new instance of `TypeMap` with a custom storage type.
    #[inline]
    pub fn custom() -> Self {
        Self(HashMap::new())
    }

    /// Returns the amount of entries in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns an indicator whether the map is empty (no entries).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Clears all entries in the map.
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Returns `true` if the map contains a value for the specified [`TypeMapKey`].
    ///
    /// ```rust
    /// use typemap_rev::{TypeMap, TypeMapKey};
    ///
    /// struct Number;
    ///
    /// impl TypeMapKey for Number {
    ///     type Value = i32;
    /// }
    ///
    /// let mut map = TypeMap::new();
    /// assert!(!map.contains_key::<Number>());
    /// map.insert::<Number>(42);
    /// assert!(map.contains_key::<Number>());
    /// ```
    #[inline]
    pub fn contains_key<T>(&self) -> bool
    where
        T: TypeMapKey,
    {
        self.0.contains_key(&TypeId::of::<T>())
    }

    /// Inserts a new value based on its [`TypeMapKey`].
    /// If the value has been already inserted, it will be overwritten
    /// with the new value.
    ///
    /// ```rust
    /// use typemap_rev::{TypeMap, TypeMapKey};
    ///
    /// struct Number;
    ///
    /// impl TypeMapKey for Number {
    ///     type Value = i32;
    /// }
    ///
    /// let mut map = TypeMap::new();
    /// map.insert::<Number>(42);
    /// // Overwrite the value of `Number` with -42.
    /// map.insert::<Number>(-42);
    /// ```
    ///
    /// [`TypeMapKey`]: trait.TypeMapKey.html
    #[inline]
    pub fn insert<T>(&mut self, value: T::Value)
    where
        T: TypeMapKey,
        T::Value: IntoBox<S>,
    {
        self.0.insert(TypeId::of::<T>(), value.into_box());
    }

    /// Retrieve the entry based on its [`TypeMapKey`]
    ///
    /// [`TypeMapKey`]: trait.TypeMapKey.html
    #[inline]
    pub fn entry<T>(&mut self) -> Entry<'_, T, S>
    where
        T: TypeMapKey,
        T::Value: IntoBox<S>,
    {
        match self.0.entry(TypeId::of::<T>()) {
            HashMapEntry::Occupied(entry) => Entry::Occupied(OccupiedEntry {
                entry,
                _marker: PhantomData,
            }),
            HashMapEntry::Vacant(entry) => Entry::Vacant(VacantEntry {
                entry,
                _marker: PhantomData,
            }),
        }
    }

    /// Retrieve a reference to a value based on its [`TypeMapKey`].
    /// Returns `None` if it couldn't be found.
    ///
    /// ```rust
    /// use typemap_rev::{TypeMap, TypeMapKey};
    ///
    /// struct Number;
    ///
    /// impl TypeMapKey for Number {
    ///     type Value = i32;
    /// }
    ///
    /// let mut map = TypeMap::new();
    /// map.insert::<Number>(42);
    ///
    /// assert_eq!(*map.get::<Number>().unwrap(), 42);
    /// ```
    ///
    /// [`TypeMapKey`]: trait.TypeMapKey.html
    #[inline]
    pub fn get<T>(&self) -> Option<&T::Value>
    where
        T: TypeMapKey,
        T::Value: IntoBox<S>,
    {
        self.0
            .get(&TypeId::of::<T>())
            .map(|b| unsafe { &*((&**b) as *const _ as *const T::Value) })
    }

    /// Retrieve a mutable reference to a value based on its [`TypeMapKey`].
    /// Returns `None` if it couldn't be found.
    ///
    /// ```rust
    /// use typemap_rev::{TypeMap, TypeMapKey};
    ///
    /// struct Number;
    ///
    /// impl TypeMapKey for Number {
    ///     type Value = i32;
    /// }
    ///
    /// let mut map = TypeMap::new();
    /// map.insert::<Number>(42);
    ///
    /// assert_eq!(*map.get::<Number>().unwrap(), 42);
    /// *map.get_mut::<Number>().unwrap() -= 42;
    /// assert_eq!(*map.get::<Number>().unwrap(), 0);
    /// ```
    ///
    /// [`TypeMapKey`]: trait.TypeMapKey.html
    #[inline]
    pub fn get_mut<T>(&mut self) -> Option<&mut T::Value>
    where
        T: TypeMapKey,
        T::Value: IntoBox<S>,
    {
        self.0
            .get_mut(&TypeId::of::<T>())
            .map(|b| unsafe { &mut *((&mut **b) as *mut _ as *mut T::Value) })
    }

    /// Removes a value from the map based on its [`TypeMapKey`].
    ///
    /// Returns a boolean indicating whether the value existed prior to its removal.
    ///
    /// ```rust
    /// use typemap_rev::{TypeMap, TypeMapKey};
    ///
    /// struct Text;
    ///
    /// impl TypeMapKey for Text {
    ///     type Value = String;
    /// }
    ///
    /// let mut map = TypeMap::new();
    /// map.insert::<Text>(String::from("Hello TypeMap!"));
    /// assert!(map.remove::<Text>().is_some());
    /// assert!(map.get::<Text>().is_none());
    /// ```
    #[inline]
    pub fn remove<T>(&mut self) -> Option<T::Value>
    where
        T: TypeMapKey,
        T::Value: IntoBox<S>,
    {
        self.0
            .remove(&TypeId::of::<T>())
            .map(|b| *unsafe { Box::from_raw(Box::into_raw(b) as *mut T::Value) })
    }
}

impl<S: ?Sized> Default for TypeMap<S> {
    fn default() -> Self {
        Self(HashMap::default())
    }
}

impl<S: ?Sized + DebuggableStorage> Debug for TypeMap<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl<S: ?Sized> Clone for TypeMap<S>
where
    Box<S>: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<S: ?Sized> Extend<(TypeId, Box<S>)> for TypeMap<S> {
    fn extend<T: IntoIterator<Item = (TypeId, Box<S>)>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

impl<S: ?Sized> IntoIterator for TypeMap<S> {
    type Item = (TypeId, Box<S>);
    type IntoIter = IntoIter<TypeId, Box<S>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<S: ?Sized> FromIterator<(TypeId, Box<S>)> for TypeMap<S> {
    fn from_iter<T: IntoIterator<Item = (TypeId, Box<S>)>>(iter: T) -> Self {
        Self(HashMap::from_iter(iter))
    }
}

/// A view into a single entry in the [`TypeMap`],
/// which may either be vacant or occupied.
///
/// This heavily mirrors the official [`Entry`] API in the standard library,
/// but not all of it is provided due to implementation restrictions. Please
/// refer to its documentations.
///
/// [`TypeMap`]: struct.TypeMap.html
/// [`Entry`]: std::collections::hash_map::Entry
pub enum Entry<'a, K, S: ?Sized = DefaultStorage>
where
    K: TypeMapKey,
{
    Occupied(OccupiedEntry<'a, K, S>),
    Vacant(VacantEntry<'a, K, S>),
}

impl<'a, K, S> Entry<'a, K, S>
where
    K: TypeMapKey,
    K::Value: IntoBox<S>,
    S: ?Sized + Any + Send + Sync,
{
    #[inline]
    pub fn or_insert(self, value: K::Value) -> &'a mut K::Value {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(value),
        }
    }

    #[inline]
    pub fn or_insert_with<F>(self, f: F) -> &'a mut K::Value
    where
        F: FnOnce() -> K::Value,
    {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(f()),
        }
    }

    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut K::Value),
    {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl<'a, K, S> Entry<'a, K, S>
where
    K: TypeMapKey,
    K::Value: Default + IntoBox<S>,
    S: ?Sized + Any + Send + Sync,
{
    #[inline]
    pub fn or_default(self) -> &'a mut K::Value {
        self.or_insert_with(<K::Value as Default>::default)
    }
}

pub struct OccupiedEntry<'a, K, S: ?Sized = DefaultStorage>
where
    K: TypeMapKey,
{
    entry: HashMapOccupiedEntry<'a, TypeId, Box<S>>,
    _marker: PhantomData<&'a K::Value>,
}

impl<'a, K, S> OccupiedEntry<'a, K, S>
where
    K: TypeMapKey,
    K::Value: IntoBox<S>,
    S: ?Sized + Any + Send + Sync,
{
    #[inline]
    pub fn get(&self) -> &K::Value {
        unsafe { &*((&**self.entry.get()) as *const _ as *const K::Value) }
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut K::Value {
        unsafe { &mut *((&mut **self.entry.get_mut()) as *mut _ as *mut K::Value) }
    }

    #[inline]
    pub fn into_mut(self) -> &'a mut K::Value {
        unsafe { &mut *((&mut **self.entry.into_mut()) as *mut _ as *mut K::Value) }
    }

    #[inline]
    pub fn insert(&mut self, value: K::Value) {
        self.entry.insert(value.into_box());
    }

    #[inline]
    pub fn remove(self) {
        self.entry.remove();
    }
}

pub struct VacantEntry<'a, K, S: ?Sized = DefaultStorage>
where
    K: TypeMapKey,
{
    entry: HashMapVacantEntry<'a, TypeId, Box<S>>,
    _marker: PhantomData<&'a K::Value>,
}

impl<'a, K, S> VacantEntry<'a, K, S>
where
    K: TypeMapKey,
    K::Value: IntoBox<S>,
    S: ?Sized + Any + Send + Sync,
{
    #[inline]
    pub fn insert(self, value: K::Value) -> &'a mut K::Value {
        let value = self.entry.insert(value.into_box());
        unsafe { &mut *((&mut **value) as *mut _ as *mut K::Value) }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    struct Counter;

    impl TypeMapKey for Counter {
        type Value = u64;
    }

    #[test]
    fn typemap_counter() {
        let mut map = TypeMap::new();

        assert_eq!(map.len(), 0);
        assert!(map.is_empty());

        map.insert::<Counter>(0);
        assert_eq!(map.len(), 1);
        assert!(!map.is_empty());

        assert_eq!(*map.get::<Counter>().unwrap(), 0);

        for _ in 0..100 {
            *map.get_mut::<Counter>().unwrap() += 1;
        }

        assert_eq!(*map.get::<Counter>().unwrap(), 100);

        map.clear();
        assert!(map.get::<Counter>().is_none());
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
    }

    #[test]
    fn typemap_entry() {
        let mut map = TypeMap::new();

        assert_eq!(map.get::<Counter>(), None);
        *map.entry::<Counter>().or_insert(0) += 42;
        assert_eq!(*map.get::<Counter>().unwrap(), 42);
    }

    struct Text;

    impl TypeMapKey for Text {
        type Value = String;
    }

    #[test]
    fn typemap_remove() {
        let mut map = TypeMap::new();

        map.insert::<Text>(String::from("foobar"));

        // This will give a &String
        assert_eq!(map.get::<Text>().unwrap(), "foobar");

        // Ensure we get an owned String back.
        let original: String = map.remove::<Text>().unwrap();
        assert_eq!(original, "foobar");

        // Ensure our String is really gone from the map.
        assert!(map.get::<Text>().is_none());
    }

    #[test]
    fn typemap_default() {
        fn ensure_default<T: Default>() {}

        ensure_default::<TypeMap>();

        let map = TypeMap::<DefaultStorage>::default();
        assert!(map.get::<Text>().is_none());
    }

    #[test]
    fn typemap_iter() {
        let mut map = TypeMap::new();
        map.insert::<Text>(String::from("foobar"));

        // creating the iterator
        let mut iterator = map.into_iter();

        // ensuring that the iterator contains our entries
        assert_eq!(iterator.next().unwrap().0, TypeId::of::<Text>());
    }

    #[test]
    fn typemap_extend() {
        let mut map = TypeMap::new();
        map.insert::<Text>(String::from("foobar"));

        let mut map_2 = TypeMap::new();
        // extending our second map with the first one
        map_2.extend(map);

        // ensuring that the new map now contains the entries from the first one
        let original = map_2.get::<Text>().unwrap();
        assert_eq!(original, "foobar");
    }

    fn is_debug<T: Debug>() {}
    fn is_clone<T: Clone>() {}

    #[test]
    fn typemap_debug() {
        is_debug::<i32>();
        is_debug::<TypeMap<dyn DebuggableStorage>>();
        is_debug::<TypeMap<dyn CloneDebuggableStorage>>();
    }

    #[test]
    fn typemap_clone() {
        is_clone::<i32>();
        is_clone::<TypeMap<dyn CloneableStorage>>();
        is_clone::<TypeMap<dyn CloneDebuggableStorage>>();

        let mut map = TypeMap::<dyn CloneableStorage>::custom();
        map.insert::<Text>(String::from("foo"));

        let map_2 = map.clone();
        assert_eq!(*map_2.get::<Text>().unwrap(), "foo");

        let mut map = TypeMap::<dyn CloneDebuggableStorage>::custom();
        map.insert::<Text>(String::from("foo"));

        let map_2 = map.clone();
        assert_eq!(*map_2.get::<Text>().unwrap(), "foo");
    }
}
