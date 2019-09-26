From Coq Require Import Init.Nat.

Inductive Fin: nat -> Type :=
| Inherit: forall n, (Fin n) -> Fin (S n)
| Cur: forall n, Fin (S n).

(* Fin0: *)

(* Fin1: *)
Check (Cur 0).

(* Fin2: *)
Check (Cur 1).
Check (Inherit 1 (Cur 0)).

(* Fin3 *)
Check (Cur 2).
Check (Inherit 2 (Cur 1)).
Check (Inherit 2 (Inherit 1 (Cur 0))).


(* dependent function *)
Fixpoint fmax (a : nat) :=
  match a with
  | 0 => Cur 0
  | S a => Inherit (S a) (fmax a)
  end.

Check (fmax 3).
Check (fmax 4).

Inductive Product (A B:Type) : Type :=
  Pr : A -> B -> Product A B.

Check (Pr nat nat 1 2).

Check prod_ind.

(* Product Type *)
Definition indProduct (A B: Type) (C: Product A B -> Type) (g : forall (a: A) (b: B), C (Pr A B a b)): forall p : Product A B, C p :=
  fun p => match p with Pr _ _ a b => g a b end.

Definition recProduct (A B: Type) (C: Type) (g : A -> B -> C) : Product A B -> C :=
  indProduct A B (fun _ => C) g.

Definition pr1 (A B : Type) : Product A B -> A :=
  recProduct A B A (fun a b => a).

Definition pr2 (A B : Type) : Product A B -> B :=
  recProduct A B B (fun a b => b).

Definition uniq (A B: Type) (p: Product A B) : Prop :=
  Pr A B (pr1 A B p) (pr2 A B p) = p.

Check (pr1 nat unit (Pr nat unit 1 tt)).
Check (pr2 nat unit (Pr nat unit 1 tt)).
Check (uniq nat unit (Pr nat unit 1 tt)).

Example uniqExample : (uniq nat unit (Pr nat unit 1 tt)).
Proof.
  reflexivity.
Qed.

(* dependent pair *)

Inductive Sigma (A: Type) (B: A -> Type):=
| Sig : forall a: A, (B a) -> Sigma A B.

Check Sig.

Inductive FinPlus: nat -> Type :=
| InheritPlus: forall n, (FinPlus n) -> FinPlus (S n)
| CurPlus: forall n, FinPlus n.

Fixpoint fPlusMax (a : nat) :=
  match a with
  | 0 => CurPlus 0
  | S a => InheritPlus (a) (fPlusMax a)
  end.

Check (Sig nat FinPlus 1 (fPlusMax 1)).

Definition indSigma (A: Type) (B: A -> Type) (C: Sigma A B -> Type) (g : forall (a: A) (b: B a), C (Sig A B a b)): forall p : Sigma A B, C p :=
  fun p => match p with Sig _ _ a b => g a b end.

Definition recSigma (A: Type) (B: A -> Type) (C: Type) (g: forall a: A, B a -> C): forall p: Sigma A B, C :=
  indSigma A B (fun _ => C) g.

Definition sig1 (A : Type) (B: A -> Type): Sigma A B -> A :=
  recSigma A B A (fun a b => a).

Definition sig2 (A : Type) (B: A -> Type): forall p: Sigma A B, B (sig1 A B p) :=
  indSigma A B (fun p => B (sig1 A B p)) (fun _ b => b).

Definition ac (A B: Type) (R: forall (a: A) (b: B), Type) (g: forall (x: A) , Sigma B (fun y => R x y)) : Sigma (A -> B) (fun f => forall x: A, R x (f x)):=
  Sig (A -> B) (fun f => forall x: A, R x (f x)) (fun x => sig1 B (fun y => R x y) (g x)) (fun x => sig2 B (fun y => R x y) (g x)).


Definition MagmaFamily (A: Type): Type := A -> A -> A.

Definition fst (A: Type) : MagmaFamily A := fun a b => a.
Definition snd (A: Type) : MagmaFamily A := fun a b => b.

(* Magma *)
Check (Sig Type MagmaFamily nat (fst nat)).
Check (Sig Type MagmaFamily nat (snd nat)).

Definition PointedMagmaFamily (A: Type): Type := (A -> A -> A) * A.

Definition natAdd: PointedMagmaFamily nat :=
  (fun (a : nat) (b: nat) => a + b, 0).

Check (Sig Type PointedMagmaFamily nat natAdd).

(* coproduct type *)

Inductive Coproduct (A B: Type): Type :=
|Inl: A -> Coproduct A B
|Inr: B -> Coproduct A B.

Check (Inl nat bool 3).

Definition indCoproduct (A B: Type) (C: Coproduct A B -> Type) (g0: forall a: A, C (Inl A B a)) (g1: forall b: B, C(Inr A B b)): forall c: Coproduct A B, C c :=
  fun c => match c with | Inl _ _ a => g0 a | Inr _ _ b => g1 b end.

Definition recCoproduct (A B C:Type) (g0: A -> C) (g1: B -> C): Coproduct A B -> C :=
  indCoproduct A B (fun _ => C) g0 g1.

(* empty type *)
Inductive Empty: Type :=.
Definition indEmpty (C : Empty -> Type) (z: Empty): C z :=
  match z with end.

(* unit type *)
Inductive Unit: Type := tt : Unit.
Definition indUnit (C : Unit -> Type) (g: forall u: Unit, C(u)) : forall x: Unit, C(x) := g.
Print Unit_ind.

(* boolean type *)
Definition Boolean : Type := Coproduct Unit Unit.
Definition b0 : Boolean := Inl Unit Unit tt.
Definition b1 : Boolean := Inr Unit Unit tt.
Definition indBoolean (C: Boolean -> Type) (g0: forall a: Unit, C (Inl Unit Unit a)) (g1: forall b: Unit, C (Inr Unit Unit b)): forall b: Boolean, C b :=
  indCoproduct Unit Unit C g0 g1.

Definition recBoolean (C: Type) (g0: C) (g1: C): Boolean -> C :=
  indBoolean (fun _ => C) (fun _ => g0) (fun _ => g1).

Definition CoproductByBoolean (A B: Type): Type := Sigma Boolean (fun x: Boolean => recBoolean Type A B x).
Definition InlByBoolean (A B: Type) (a: A) : CoproductByBoolean A B :=
  Sig Boolean (fun x: Boolean => recBoolean Type A B x) b0 a.
Definition InrByBoolean (A B: Type) (b: B) : CoproductByBoolean A B :=
  Sig Boolean (fun x: Boolean => recBoolean Type A B x) b1 b.

Definition ProductByBoolean (A B: Type): Type := (forall x: Boolean, recBoolean Type A B x).
Definition PrByBoolean (A B: Type) (a: A) (b : B) : ProductByBoolean A B :=
  indBoolean (fun x => recBoolean Type A B x) (fun _ => a) (fun _ => b).
Definition Pr1ByBoolean (A B: Type) (p: ProductByBoolean A B): A := p b0.
Definition Pr2ByBoolean (A B: Type) (p: ProductByBoolean A B): B := p b1.

(* nat type *)

Inductive Natural : Type :=
| n0: Natural
| nsucc: forall n: Natural, Natural.

(* work around, as coq fixpoint functions require the first arg to be a structurally snaller one. *)
Definition indNatural (C: Natural -> Type) (g0: C n0) (g1: (forall n: Natural, C n -> C (nsucc n))): forall n: Natural, C n :=
  fix aux (n: Natural) : C n :=
    match n with | n0 => g0 | nsucc n' => g1 n' (aux n') end.

Definition recNatural (C: Type) (g0: C) (g1: Natural -> C -> C): Natural -> C :=
  indNatural (fun _ => C) g0 g1.

Definition addNatural: Natural -> Natural -> Natural :=
  recNatural (Natural -> Natural) (fun b => b) (fun _ f b => nsucc (f b)).

Definition addProperty0 : forall n, addNatural n0 n = n := fun _ => eq_refl.
Definition addProperty1 : forall n m, addNatural (nsucc m) n = nsucc (addNatural m n) := fun _ _ => eq_refl.

Definition doubleNatural: Natural -> Natural:=
  recNatural Natural n0 (fun _ n => nsucc (nsucc n)).

Definition assoc0: forall j k: Natural, addNatural n0 (addNatural j k) = addNatural (addNatural n0 j) k :=
  fun _ _ => eq_refl.

Definition ap (A B: Type) (f: A -> B) (x y: A) : x = y -> f x = f y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Print ap.

Definition apSucc (a b: Natural) : a = b -> nsucc a = nsucc b :=
  ap Natural Natural nsucc a b.

Definition assocs (i : Natural) (h: forall j k: Natural, addNatural i (addNatural j k) = addNatural (addNatural i j) k) : (forall j k: Natural, addNatural (nsucc i) (addNatural j k) = addNatural (addNatural (nsucc i) j) k) :=
  fun j k => apSucc (addNatural i (addNatural j k)) (addNatural (addNatural i j) k) (h j k).

Definition assoc: forall i, forall j k, addNatural i (addNatural j k) = addNatural (addNatural i j) k :=
  indNatural (fun i => forall j k, addNatural i (addNatural j k) = addNatural (addNatural i j) k) assoc0 assocs.

(* propositions as types *)

Definition LogicTrue : Type := Unit.
Definition LogicFalse : Type := Empty.
Definition LogicAnd : Type -> Type -> Type := Product.
Definition LogicOr : Type -> Type -> Type := Coproduct.
Definition LogicIf : Type -> Type -> Type := fun A B => A -> B.
Definition LogicIff : Type -> Type -> Type := fun A B => Product (LogicIf A B) (LogicIf B A).
Definition LogicNot : Type -> Type := fun A => LogicIf A LogicFalse.

Definition PropExample (A B: Type): LogicIf (LogicAnd (LogicNot A) (LogicNot B)) (LogicNot (Coproduct A B)) :=
  indProduct (LogicNot A) (LogicNot B) (fun _ => (LogicNot (Coproduct A B)))
             (fun notA notB => indCoproduct A B (fun _ => LogicFalse)(fun a => match notA a with end) (fun b => match notB b with end)).

Print PropExample.

Definition LogicExists := Sigma.

Definition PropExample2 (A: Type) (P: A -> Type) (Q: A -> Type): (forall x: A, Product (P x) (Q x)) -> (Product (forall x: A, P x) (forall x: A, Q x)) :=
  fun pre => Pr (forall x: A, P x) (forall x: A, Q x)
             (fun x => recProduct (P x) (Q x) (P x) (fun x _ => x) (pre x))
             (fun x => recProduct (P x) (Q x) (Q x) (fun _ y => y) (pre x)).

Definition LessThanEq (n m: Natural): Type := Sigma Natural (fun k => addNatural n k = m).

Print LessThanEq.

Definition LessThan (n m: Natural) : Type := Product (LessThanEq n m) (LogicNot (n = m)).
Check LessThan.

Definition LteExample : LessThanEq n0 n0 :=
  Sig Natural (fun k => addNatural n0 k = n0) n0 eq_refl.

Lemma zero_is_not_one: (LogicNot (n0 = (nsucc n0))).
Proof.
  unfold LogicNot.
  unfold LogicIf.
  intros.
  inversion H.
Qed.

Print zero_is_not_one.

Definition LtExample : LessThan n0 (nsucc n0) :=
  Pr _ _ (Sig Natural (fun k => addNatural n0 k = (nsucc n0)) (nsucc n0) eq_refl) zero_is_not_one.

Definition Semigroup: Type := Sigma Type (fun A => Sigma (A -> A -> A) (fun m => forall x y z: A, m x (m y z) = m (m x y) z)).

Lemma assocNatural: forall x y z : Natural, addNatural x (addNatural y z) = addNatural (addNatural x y) z.
Proof.
  intro x.
  induction x; intros.
  + reflexivity.
  + simpl. rewrite (IHx y z). reflexivity.
Qed.

Definition SemigroupExample: Semigroup :=
  Sig Type (fun A => Sigma (A -> A -> A) (fun m => forall x y z: A, m x (m y z) = m (m x y) z)) Natural
      (Sig (Natural -> Natural -> Natural) (fun m => forall x y z: Natural, m x (m y z) = m (m x y) z) addNatural assocNatural).

Print SemigroupExample.

(* identity type. *)
Inductive Identity (A: Type): A -> A -> Type :=
| idRefl: forall a: A, Identity A a a.

(* path induction *)
(* induction rule *)
Definition indId (A: Type) (C: forall x y: A, Identity A x y -> Type) (f: forall x: A, C x x (idRefl A x)) : forall x y: A, forall p: Identity A x y, C x y p :=
  fun _ _ p => match p in (Identity _ x' y') return C x' y' p with
            | idRefl _ a => f a
            end.

(* indiscernibility of identils *)
(* rewrite rule *)

Definition idRewrite (A: Type) (C: A -> Type): forall a b: A, forall p: Identity A a b, (C a) -> (C b) :=
  fun _ _ p => match p in Identity _ a b return C a -> C b with
               | idRefl _ _ => fun x => x
               end.

Definition idRewrite' (A: Type) (C: A -> Type): forall a b: A, forall p: Identity A a b, (C a) -> (C b) :=
  indId A (fun x y _ => C x -> C y) (fun _ => fun x => x).

(* base path induction *)

Definition baseIndId (A: Type) (a: A) (C: forall x: A, Identity A a x -> Type) (c: C a (idRefl A a)) : forall x: A, forall p: Identity A a x, C x p :=
  fun x p =>
  (fun _ p => match p in Identity _ a x return forall C': forall x: A, Identity A a x -> Type, forall c: C' a (idRefl A a), C' x p with
          | idRefl _ _ => fun _ p => p 
           end) x p C c.

(* baseInd is equivalent with ind *)

Definition baseIndId' (A: Type) (a: A) (C: forall x: A, Identity A a x -> Type) (c: C a (idRefl A a)) (x: A) (p: Identity A a x) : C x p :=
  (indId A (fun a x p => forall C': forall x: A, Identity A a x -> Type, forall c' : C' a (idRefl A a), C' x p) (fun _ _ p => p)) a x p C c.

Definition indId' (A: Type) (C: forall x y: A, Identity A x y -> Type) (f: forall x: A, C x x (idRefl A x)) : forall x y: A, forall p: Identity A x y, C x y p :=
  fun x => baseIndId A x (fun y => C x y) (f x).

(* disequality *)
Definition disequal (A: Type) := forall x y: A, LogicNot (Identity A x y).