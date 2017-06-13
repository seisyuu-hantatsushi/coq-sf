Require Export Poly.

Check (2 + 2 = 4).

Check (ble_nat 3 2 = false).

Check (2 + 2 = 5).

Theorem plus_2_2_is_4:
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact :
  Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true:
  plus_fact.
Proof. reflexivity. Qed.

Definition even (n:nat) : Prop :=
  evenb n = true.

Check even.
Check (even 4).
Check (even 3).

Definition even_n__even_SSn (n:nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat -> Prop := between 13 19.
Check teen.

Definition true_for_zero (P:nat -> Prop) : Prop := P 0.

Definition true_for_n__true_for_Sn (P:nat -> Prop) (n:nat) : Prop :=
  P n -> P (S n).

Definition preserved_by_S (P:nat -> Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P:nat -> Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P:nat -> Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

Check our_nat_induction.

Inductive good_day: day -> Prop :=
| gd_sat : good_day saturday
| gd_sun : good_day sunday.

