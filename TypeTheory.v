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
  recProduct A B A (fun a => fun b => a).

Definition pr2 (A B : Type) : Product A B -> B :=
  recProduct A B B (fun a => fun b => b).

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
  recSigma A B A (fun a => fun b => a).

Definition sig2 (A : Type) (B: A -> Type): forall p: Sigma A B, B (sig1 A B p) :=
  indSigma A B (fun p => B (sig1 A B p)) (fun _ b => b).

Definition ac (A B: Type) (R: forall (a: A) (b: B), Type) (g: forall (x: A) , Sigma B (fun y => R x y)) : Sigma (A -> B) (fun f => forall x: A, R x (f x)):=
  Sig (A -> B) (fun f => forall x: A, R x (f x)) (fun x => sig1 B (fun y => R x y) (g x)) (fun x => sig2 B (fun y => R x y) (g x)).


Definition MagmaFamily (A: Type): Type := A -> A -> A.

Definition fst (A: Type) : MagmaFamily A := fun a => fun b => a.
Definition snd (A: Type) : MagmaFamily A := fun a => fun b => b.

(* Magma *)
Check (Sig Type MagmaFamily nat (fst nat)).
Check (Sig Type MagmaFamily nat (snd nat)).

Definition PointedMagmaFamily (A: Type): Type := (A -> A -> A) * A.

Definition natAdd: PointedMagmaFamily nat :=
  (fun a : nat => fun b: nat => a + b, 0).

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
