---
name: fstar-stdlib
description: F* standard library — Seq, List, Map, Set, Option, Classical, Squash.
---

# F\* Standard Library

> **Version:** pinned to F\* ≤ 2025.12.15 (Low*/KaRaMeL era).
> For ≥ v2026.09.20 (Custard/Pulse, `krml`/Low* removed), see
> [`fstar-2026.09.20`](../fstar-2026.09.20/SKILL.md).
> Extracted from the full F* skill.  Cross-reference: [fstar index](../SKILL.md).

---

## 1. Sequence (Seq) Type

`FStar.Seq` provides length-indexed sequences (logical, not runtime arrays).

### Core API (Seq.Base)

```fstar
type seq (a:Type)  (* abstract *)

val length    : #a:Type -> seq a -> Tot nat
val index     : #a:Type -> s:seq a -> i:nat{i < length s} -> Tot a
val create    : #a:Type -> nat -> a -> Tot (seq a)
val empty     : #a:Type -> Tot (s:seq a{length s = 0})
val upd       : #a:Type -> s:seq a -> n:nat{n < length s} -> a -> Tot (seq a)
val append    : #a:Type -> seq a -> seq a -> Tot (seq a)
val slice     : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} -> Tot (seq a)
val cons      : #a:Type -> x:a -> s:seq a -> Tot (seq a)
val equal     : #a:Type -> s1:seq a -> s2:seq a -> Tot prop
val eq        : #a:eqtype -> s1:seq a -> s2:seq a -> Tot bool

(* Conversion *)
val seq_to_list : #a:Type -> s:seq a -> Tot (l:list a{List.length l == length s})
val seq_of_list : #a:Type -> l:list a -> Tot (s:seq a{List.length l == length s})
```

### Key Lemmas

```fstar
val lemma_eq_elim : #a:Type -> s1 s2:seq a ->
  Lemma (requires equal s1 s2) (ensures s1 == s2)

val lemma_eq_intro : #a:Type -> s1 s2:seq a ->
  Lemma (requires length s1 = length s2 /\ (forall i. index s1 i == index s2 i))
        (ensures equal s1 s2)

val lemma_index_app1 : #a:Type -> s1 s2:seq a -> i:nat{i < length s1} ->
  Lemma (index (append s1 s2) i == index s1 i)

val lemma_index_app2 : #a:Type -> s1 s2:seq a ->
  i:nat{i < length s1 + length s2 /\ length s1 <= i} ->
  Lemma (index (append s1 s2) i == index s2 (i - length s1))

val lemma_index_slice : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} ->
  k:nat{k < j - i} -> Lemma (index (slice s i j) k == index s (k + i))

val lemma_len_slice : #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} ->
  Lemma (length (slice s i j) = j - i)
```

### Common Patterns

```fstar
(* Slice equality without explicit forall *)
let lemma_slice_append_left (#a:Type) (s1 s2: Seq.seq a) : Lemma
  (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
  = Seq.lemma_eq_intro
      (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1))
      s1
(* SMT handles element-wise equality automatically *)

(* Associativity bridging *)
Seq.append_assoc (Seq.create 1 b) s_tl rest
(* Now SMT sees: (create 1 b ++ s_tl) ++ rest == create 1 b ++ (s_tl ++ rest) *)
```

### Gotchas

- `Seq.slice` has refinement `j:nat{i <= j /\ j <= length s}`. SMT may fail to prove `j <= length s` when `j` is a `U32.v` value. Use `forall`+`Seq.index` patterns for buffer preservation instead.
- `seq_of_list` return type refinement: `List.length l == length s`. This refinement is NOT automatically propagated through `let` bindings — call `lemma_seq_of_list_length` to expose it.
- `Seq.cons x s` is definitionally `Seq.append (Seq.create 1 x) s`.

---

## 2. List Operations

### FStar.List.Tot.Base

```fstar
val length    : list 'a -> Tot nat
val hd        : l:list 'a{Cons? l} -> Tot 'a
val tail      : l:list 'a{Cons? l} -> Tot (list 'a)
val index     : #a:Type -> l:list a -> i:nat{i < length l} -> Tot a
val append    : list 'a -> list 'a -> Tot (list 'a)     (* operator @@ *)
val rev       : list 'a -> Tot (list 'a)
val flatten   : list (list 'a) -> Tot (list 'a)
val map       : ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
val fold_left : ('a -> 'b -> Tot 'a) -> 'a -> l:list 'b -> Tot 'a (decreases l)
val fold_right: ('a -> 'b -> Tot 'b) -> list 'a -> 'b -> Tot 'b
val filter    : f:('a -> Tot bool) -> l:list a -> Tot (list a)
val for_all   : ('a -> Tot bool) -> list 'a -> Tot bool
val existsb   : f:('a -> Tot bool) -> list a -> Tot bool
val mem       : #a:eqtype -> a -> list a -> Tot bool
val memP      : #a:Type -> x:a -> l:list a -> Tot Type0   (* propositional *)
val find      : f:('a -> Tot bool) -> list a -> Tot (option (x:a{f x}))
val partition : f:('a -> Tot bool) -> list a -> Tot (list a & list a)
val sortWith  : ('a -> 'a -> Tot int) -> l:list a -> Tot (list a) (decreases (length l))
val splitAt   : n:nat -> l:list a -> Tot (list a & list a)
val unsnoc    : #a:Type -> l:list a{length l > 0} -> Tot (list a & a)
val unzip     : list ('a & 'b) -> Tot (list 'a & list 'b)
val unzip3    : list ('a & 'b & 'c) -> Tot (list 'a & list 'b & list 'c)
```

### Key Lemmas

```fstar
val append_length  : l1 l2:list 'a -> Lemma (length (l1@l2) = length l1 + length l2)
val append_assoc   : l1 l2 l3:list 'a -> Lemma ((l1@l2)@l3 == l1@(l2@l3))
val append_l_nil   : l:list 'a -> Lemma (l@[] == l)
val append_nil_l   : l:list 'a -> Lemma ([]@l == l)
val mem_memP       : #a:eqtype -> x:a -> l:list a -> Lemma (mem x l <==> memP x l)
```

### Hard List Lemmas SMT Cannot Prove

**Index on append prefix** — requires explicit structural induction on `l1`:

```fstar
let rec lemma_index_append_prefix (#a:Type) (l1 l2: list a) (i: nat) : Lemma
  (requires i < List.Tot.length l1)
  (ensures List.Tot.index (l1 @ l2) i == List.Tot.index l1 i)
  (decreases l1)
  = match l1 with
    | [] -> ()
    | h :: t -> if i = 0 then () else lemma_index_append_prefix t l2 (i - 1)
```

**Index on last element of append** — must prove length bound alongside equality:

```fstar
let rec lemma_index_append_singleton (#a:Type) (l1: list a) (x: a) : Lemma
  (ensures
    List.Tot.length l1 < List.Tot.length (l1 @ [x]) /\
    List.Tot.index (l1 @ [x]) (List.Tot.length l1) == x)
  (decreases l1)
  = List.Tot.append_length l1 [x];
    match l1 with | [] -> () | h :: t -> lemma_index_append_singleton t x
```

---

## 3. Map Type (FStar.Map)

```fstar
val t (key:eqtype) (value:Type) : Type

val sel      : #key:eqtype -> #value:Type -> t key value -> key -> Tot value
val upd      : #key:eqtype -> #value:Type -> t key value -> key -> value -> Tot (t key value)
val const    : #key:eqtype -> #value:Type -> value -> Tot (t key value)
val domain   : #key:eqtype -> #value:Type -> t key value -> Tot (Set.set key)
val contains : #key:eqtype -> #value:Type -> t key value -> key -> Tot bool
val restrict : #key:eqtype -> #value:Type -> Set.set key -> t key value -> Tot (t key value)
```

**Implementation**: Maps use `FStar.FunctionalExtensionality` — domain-restricted functions.

### Key Lemmas

```fstar
val lemma_SelUpd1      : (* sel (upd m k v) k == v *)
val lemma_SelUpd2      : (* k1 != k2 ==> sel (upd m k2 v) k1 == sel m k1 *)
val lemma_SelConst     : (* sel (const v) k == v *)
val lemma_ContainsDom  : (* contains m k = Set.mem k (domain m) *)
val lemma_equal_elim   : (* equal m1 m2 <==> m1 == m2 *)
val lemma_equal_intro  : (* pointwise equal + same domain ==> equal *)
```

---

## 4. Set Type (FStar.Set)

```fstar
val set (a:eqtype) : Type0     (* = a ^-> bool *)

val mem        : #a:eqtype -> x:a -> s:set a -> Tot bool
val empty      : #a:eqtype -> Tot (set a)
val singleton  : #a:eqtype -> x:a -> Tot (set a)
val union      : #a:eqtype -> set a -> set a -> Tot (set a)
val intersect  : #a:eqtype -> set a -> set a -> Tot (set a)
val complement : #a:eqtype -> set a -> Tot (set a)

(* Derived *)
let disjoint (#a:eqtype) (s1 s2: set a) = equal (intersect s1 s2) empty
let subset  (#a:eqtype) (s1 s2: set a) = forall x. mem x s1 ==> mem x s2
let add     (#a:eqtype) (x:a) (s:set a) = union s (singleton x)
let remove  (#a:eqtype) (x:a) (s:set a) = intersect s (complement (singleton x))

(* Extensionality *)
val lemma_equal_intro : #a:eqtype -> s1 s2:set a ->
  Lemma (requires (forall x. mem x s1 = mem x s2)) (ensures equal s1 s2)
val lemma_equal_elim  : #a:eqtype -> s1 s2:set a ->
  Lemma (requires equal s1 s2) (ensures s1 == s2)
```

---

## 5. Option Utilities (FStar.Option)

```fstar
val isNone : option 'a -> Tot bool
val isSome : option 'a -> Tot bool
val map    : ('a -> ML 'b) -> option 'a -> ML (option 'b)
val mapTot : ('a -> Tot 'b) -> option 'a -> Tot (option 'b)
val get    : option 'a -> ML 'a    (* fails if None *)
```

---

## 6. Classical Logic (FStar.Classical)

```fstar
val excluded_middle (p: Type) : Lemma (p \/ ~p)
val forall_intro (#a: Type) (#p: (a -> GTot Type)) (f: (x: a -> Lemma (p x))) :
  Lemma (forall x. p x)
val exists_intro (#a: Type) (p: (a -> Type)) (witness: a) :
  Lemma (requires p witness) (ensures exists x. p x)
val impl_intro (#p #q: Type0) (f: (p -> Lemma q)) : Lemma (p ==> q)
val move_requires (#a: Type) (#p #q: (a -> Type))
  (f: (x: a -> Lemma (requires p x) (ensures q x))) (x: a) : Lemma (p x ==> q x)
val forall_intro_with_pat ... : Lemma (forall x.{:pattern (pat x)} p x)
```

---

## 7. Squash (FStar.Squash)

```fstar
val return_squash (#a: Type) (x: a) : Tot (squash a)
val bind_squash (#a #b: Type) (x: squash a) (f: (a -> GTot (squash b))) : Tot (squash b)
val get_proof (p: Type) : Pure (squash p) (requires p) (ensures fun _ -> True)
val give_proof (#p: Type) (x: squash p) : Pure unit True (ensures fun _ -> p)
val map_squash (#a #b: Type) (x: squash a) (f: (a -> GTot b)) : Tot (squash b)
```

---

## 8. Functional Extensionality

```fstar
open FStar.FunctionalExtensionality

let feq (#a: Type) (#b: (a -> Type)) (f g: arrow a b) =
  forall x. f x == g x

val extensionality (a: Type) (b: (a -> Type)) (f g: arrow a b) :
  Lemma (ensures (feq #a #b f g <==> on_domain a f == on_domain a g))

let (^->) (a b: Type) = f: arrow a b {on_domain a f == f}
```

---

## 9. Algebra Types

### Monoid (FStar.Algebra.Monoid)

```fstar
unopteq type monoid (m:Type) =
  | Monoid :
    unit:m ->
    mult:(m -> m -> m) ->
    right_unitality:squash (right_unitality_lemma m unit mult) ->
    left_unitality:squash (left_unitality_lemma m unit mult) ->
    associativity:squash (associativity_lemma m mult) ->
    monoid m

(* Pre-built instances *)
val nat_plus_monoid : monoid nat
val int_plus_monoid : monoid int
val conjunction_monoid : monoid prop
val disjunction_monoid : monoid prop
val bool_and_monoid : monoid bool
val bool_or_monoid : monoid bool
val bool_xor_monoid : monoid bool
```

---

## 10. Ghost / Erased Types

```fstar
[@@ erasable]
new val erased (a: Type u#a) : Type u#a

val reveal: #a: Type u#a -> erased a -> GTot a     (* Only in Ghost *)
val hide  : #a: Type u#a -> a -> Tot (erased a)
```
