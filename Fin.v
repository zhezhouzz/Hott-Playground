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
  fun p => indProduct A B (fun _ => C) g p.

Definition pr₁ (A B : Type) : Product A B -> A :=
  recProduct A B A (fun a => fun b => a).

Definition pr₂ (A B : Type) : Product A B -> B :=
  recProduct A B B (fun a => fun b => b).

Definition uniq (A B: Type) (p: Product A B) : Prop :=
  Pr A B (pr₁ A B p) (pr₂ A B p) = p.

Check (pr₁ nat unit (Pr nat unit 1 tt)).
Check (pr₂ nat unit (Pr nat unit 1 tt)).
Check (uniq nat unit (Pr nat unit 1 tt)).

Example uniqExample : (uniq nat unit (Pr nat unit 1 tt)).
Proof.
  reflexivity.
Qed.

