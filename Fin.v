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

Fixpoint fmax (a : nat) :=
  match a with
  | 0 => Cur 0
  | S a => Inherit (S a) (fmax a)
  end.

Check (fmax 3).
Check (fmax 4).