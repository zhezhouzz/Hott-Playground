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

(* Inductive Product (A B:Type) : Type := *)
(*   Pr : A -> B -> Product A B. *)

(* Check (1, 2). *)
(* Check (Pr 1 2). *)


(* Product Type *)
Definition indProduct (A B: Type) (C: prod A B -> Type) (p: prod A B) (g : A -> B -> C p): C p :=
  match p with pair a b => g a b end.

Definition recProduct (A B: Type) (C: Type) (g : A -> B -> C) : prod A B -> C :=
  fun p => indProduct A B (fun _ => C) p g.

Definition pr₁ (A B : Type) : prod A B -> A :=
  recProduct A B A (fun a => fun b => a).

Definition pr₂ (A B : Type) : prod A B -> B :=
  recProduct A B B (fun a => fun b => b).

Definition uniq (A B: Type) (p: prod A B) : Prop :=
  (pr₁ A B p, pr₂ A B p) = p.

Check (pr₁ nat unit (1, tt)).
Check (pr₂ nat unit (1, tt)).
Check (uniq nat unit (1, tt)).

Example uniqExample : (uniq nat unit (1, tt)).
Proof.
  reflexivity.
Qed.

