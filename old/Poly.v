Require Export List.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type): Type:=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil _ => 0
    | cons _ h t => S (length X t)
  end.

Example test_length1 :
  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
  length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil _ => l2
    | cons _ h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : list X :=
  match l with
    | nil _ => cons X v (nil X)
    | cons _ h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
    | nil _ => nil X
    | cons _ h t => snoc X (rev X t) h
  end.

Example test_rev1:
  rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil _ => l2
    | cons _ h t => cons X h (app' X t l2)
  end.

Check app.
Check app'.

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
    | nil _ => 0
    | cons _ h t => S (length' _ t)
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length'' t)
  end.

Definition mynil : list nat := nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1, 2, 3].

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
  match count with
    | O => nil
    | S count' => n :: (repeat X n count')
  end.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof.
  simpl. reflexivity.
Qed.

Theorem nil_app:
  forall X:Type, forall l:list X,
    app [] l = l.
Proof.
  simpl. reflexivity.
Qed.

Theorem rev_snoc:
  forall X:Type, forall v:X, forall s:list X,
    rev (snoc s v) = v :: (rev s).
Proof.
  intros.
  induction s as [|s0 s'].
  Case "s=nil".
  simpl.
  reflexivity.
  Case "s=s0::s'".
  simpl.
  rewrite -> IHs'.
  simpl.
  reflexivity.
Qed.

Theorem snoc_with_append :
  forall X:Type,
  forall l1 l2 : list X,
  forall v : X,
    snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros.
  induction l1 as [| h l1'].
  Case "l1=nil".
  simpl.
  reflexivity.
  Case "l1=h::l1".
  simpl.
  rewrite -> IHl1'.
  reflexivity.
Qed.

Inductive prod (X Y:Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst ( X Y : Type ) (p : X*Y): X :=
  match p with (x , y) => x end.

Definition snd ( X Y : Type ) (p : X*Y): Y :=
  match p with (x , y) => y end.

Fixpoint combine {X Y:Type} (lx:list X) (ly:list Y)
: list (X*Y) :=
  match (lx, ly) with
    | ([],_) => []
    | (_,[]) => []
    | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Fixpoint combine' {X Y:Type} (lx:list X) (ly:list Y)
: list (X*Y) :=
  match lx, ly with
    | [],_ => []
    | _,[] => []
    | x::tx,y::ty => (x,y)::(combine' tx ty)
  end.

Check @combine.

Eval simpl in (combine [1,2] [false,false,true,true]).

Fixpoint fstlist {X Y:Type} (l : list (X*Y)) : (list X)
  := match l with
       | nil => nil
       | h::tl => (fst X Y h) :: fstlist tl
     end.

Fixpoint sndlist {X Y:Type} (l : list (X*Y)) : (list Y)
  := match l with
       | nil => nil
       | h::tl => (snd X Y h) :: sndlist tl
     end.

Fixpoint split {X Y:Type} (l : list (X*Y)) : (list X) * (list Y)
  := (fstlist l , sndlist l).

Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof.
  simpl.
  reflexivity.
Qed.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X:Type} (n : nat) (l : list X)
: option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.

Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.

Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X := index 0 l.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1,2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [[1],[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3: plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus3': doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus3'': doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z:Type}
           (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x , y).

Definition prod_uncurry {X Y Z:Type}
           (f : X -> Y -> Z) (p: X*Y) : Z := f (fst X Y p) (snd X Y p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry:
  forall (X Y Z:Type) (f: X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry:
  forall (X Y Z:Type) (f: (X*Y) -> Z) (p: X*Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  unfold prod_uncurry.
  unfold prod_curry.
  destruct p.
  simpl.
  reflexivity.
Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
    | [] => []
    | h::t => if test h then h :: (filter test t)
              else filter test t
  end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1 [[1,2],[3],[4],[5,6,7],[],[8]] = [[3],[4],[8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1)
         [[1,2],[3],[4],[5,6,7],[],[8]]
  = [[3],[4],[8]].
Proof.
  reflexivity.
Qed.

Definition filter_even_gt7 (l: list nat) : list nat :=
  filter (fun n => if evenb n then negb (ble_nat n 7) else false) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof.
  unfold filter_even_gt7.
  simpl.
  reflexivity.
Qed.

Definition partition {X:Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof.
  reflexivity.
Qed.

Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof.
  reflexivity.
Qed.

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h)::(map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof.
  reflexivity.
Qed.

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.


Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.

Lemma snoc_map:
  forall (X Y: Type) (f : X -> Y) (l : list X) (x : X),
    map f (snoc l x) = snoc (map f l) (f x).
  Proof.
    intros X Y f l.
    induction l as [|l0 l'].
    Case "l=[]".
    simpl.
    reflexivity.
    Case "l=l0::l'".
    simpl.
    intros.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l as [| l0 l'].
  Case "l=[]".
  simpl.
  reflexivity.
  Case "l=l0::l'".
  simpl.
  rewrite -> snoc_map.
  rewrite -> IHl'.
  reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
: (list Y) :=
  match l with
    | [] => []
    | h::t => (f h) ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof.
  simpl.
  reflexivity.
Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint map' (X Y:Type) (f:X->Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h)::(map f t)
  end.

Example test_map'1: map' nat nat (plus 3) [2,0,2] = [5,3,5].
Proof.
  reflexivity.
Qed.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) :Y :=
  match l with
    | nil => b
    | h::t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X: Type} (f: nat -> X) (k:nat) (x:X) : nat -> X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.
Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  reflexivity.
Qed.

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros n m H.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

Theorem override_eq :
  forall {X:Type} x k (f:nat -> X), (override f k x) k = x.
Proof.
  intros.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.


Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros.
  unfold override.
  rewrite -> H0.
  rewrite -> H.
  reflexivity.
Qed.

Theorem eq_add_S :
  forall (n m:nat), S n = S m -> n = m.
Proof.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.

Theorem silly4 :
  forall (n m : nat), [n] = [m] -> n = m.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.

Theorem silly5 :
  forall (n m o: nat), [n,m] = [o,o] -> [n] = [m].
  intros n m o eq.
  inversion eq.
  reflexivity.
Qed.

Theorem sillyex1 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
  intros.
  inversion H0.
  reflexivity.
Qed.

Theorem silly6 :
  forall (n:nat), S n = 0 -> 2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem silly7 :
  forall (n m:nat), false = true -> [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.


Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros.
  inversion H.
Qed.

Lemma eq_remove_S :
  forall n m, n = m -> S n = S m.
Proof.
  intros n m eq.
  rewrite -> eq.
  reflexivity.
Qed.

Theorem beq_nat_eq:
  forall n m, true = beq_nat n m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n=0".
  intros m.
  destruct m as [| m'].
  SCase "m=0".
  reflexivity.
  SCase "m=S m".
  simpl.
  intros contra.
  inversion contra.
  Case "n=S n".
  intros m.
  destruct m as [| m'].
  SCase "m=0".
  simpl.
  intros contra.
  inversion contra.
  SCase "m=S m".
  simpl.
  intros.
  apply eq_remove_S.
  apply IHn'.
  apply H.
Qed.

Theorem beq_nat_eq':
  forall n m, true = beq_nat n m -> n = m.
Proof.
  intros m. induction m as [| m'].
  simpl.
  destruct m.
  intros.
  reflexivity.
  intros.
  inversion H.
  destruct m.
  intros.
  inversion H.
  simpl.
  intros.
  apply eq_remove_S.
  apply IHm'.
  apply H.
Qed.

Theorem length_snoc' :
  forall (X : Type) (v : X) (l : list X) (n : nat),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l.
  induction l as [| v' l'].
  Case "l=[]".
  intros n eq.
  rewrite <- eq.
  simpl.
  reflexivity.
  Case "l=v'::l'".
  intros n eq.
  simpl.
  destruct n as [| n'].
  SSCase "n=0".
  inversion eq.
  SSCase "n=S n'".
  apply eq_remove_S.
  apply IHl'.
  inversion eq.
  reflexivity.
Qed.

Theorem beg_nat_0_l:
  forall n, true = beq_nat 0 n -> 0 = n.
Proof.
  intros n.
  apply beq_nat_eq.
Qed.

Theorem beg_nat_0_r:
  forall n, true = beq_nat n 0 -> 0 = n.
Proof.
  intros n H.
  apply beg_nat_0_l.
  rewrite H.
  SearchAbout (beq_nat _ _).
  apply beq_nat_sym.
Qed.

Theorem double_injective:
  forall n m, double n = double m -> n = m.
Proof.
  intros n.
  induction n as [|n'].
  Case "n=0".
  simpl.
  intros m eq.
  destruct m as [|m'].
  SCase "m=0".
  reflexivity.
  SCase "m=S m'".
  inversion eq.
  Case "n=S n'".
  intros m eq.
  destruct m as [|m'].
  SCase "m=0".
  inversion eq.
  apply eq_remove_S.
  apply IHn'.
  inversion eq.
  reflexivity.
Qed.

Theorem S_inj:
  forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros.
  simpl in H.
  apply H.
Qed.

Theorem silly3' :
  forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

Theorem plus_n_n_injective:
  forall n m,  n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n=0".
  destruct m as [| m'].
  SCase "m=0".
  reflexivity.
  SCase "m=S m'".
  intro contra.
  inversion contra.
  Case "n=S n'".
  destruct m as [| m'].
  SCase "m=0".
  intro contra.
  inversion contra.
  SCase "m=S m'".
  intro H.
  apply eq_remove_S.
  apply IHn'.
  simpl in H.
  inversion H.
  rewrite <- plus_n_Sm in H1.
  rewrite <- plus_n_Sm in H1.
  inversion H1.
  reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else
    if beq_nat n 5 then false
    else false.

Theorem sillyfun_false:
  forall (n : nat), sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  Case "beq_nat n 3 = true".
  reflexivity.
  Case "beq_nat n 3 = false".
  destruct (beq_nat n 5).
  SCase "beq_nat n 5 = true".
  reflexivity.
  SCase "beq_nat n 5 = false".
  reflexivity.
Qed.

Theorem override_shadow:
  forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
    (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true".
  reflexivity.
  Case "beq_nat k1 k2 = false".
  reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else
    if beq_nat n 5 then true
    else false.

Theorem sillyfun1_odd:
  forall (n:nat), sillyfun1 n = true -> oddb n = true.
Proof.                         
  intros n eq.
  unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct e3.
  Case "e3 = true".
  apply beq_nat_eq in Heqe3.
  rewrite -> Heqe3.
  reflexivity.
  Case "e3 = false".
  remember (beq_nat n 5) as e5.
  destruct e5.
  SCase "e5 = true".
  apply beq_nat_eq in Heqe5.
  rewrite Heqe5.
  reflexivity.
  SCase "e5 = false".
  inversion eq.
Qed.

Theorem override_same:
  forall {X:Type} x1 k1 k2 (f : nat -> X),
    f k1 = x1 ->
    (override f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold override.
  remember (beq_nat k1 k2) as ek.
  destruct ek.
  Case "ek = true".
  apply beq_nat_eq in Heqek.
  rewrite Heqek in H.
  rewrite H.
  reflexivity.
  Case "ek = false".
  reflexivity.
Qed.

Theorem filter_exercise:
  forall (X:Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l lf.
  induction l.
  Case "l=[]".
  simpl.
  intros.
  inversion H.
  Case "l=l0::l'".
  intros.
  simpl in H.
  remember (test x0).
  destruct b.
  SCase "b=true".
  inversion H.
  rewrite <- H1.
  symmetry.
  apply Heqb.
  SCase "b=false".
  apply IHl.
  apply H.
Qed.

Example trans_eq_example:
  forall (a b c d e f : nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem trans_eq:
  forall {X:Type} (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example':
  forall (a b c d e f : nat),
    [a, b] = [c, d] ->
    [c, d] = [e, f] ->
    [a, b] = [e, f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c,d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise:
  forall (n m o p:nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  symmetry in eq1.
  apply trans_eq with m.
  apply eq2.
  symmetry.
  apply eq1.
Qed.

Theorem beq_nat_trans:
  forall (n m p:nat),
    true = beq_nat n m ->
    true = beq_nat m p ->
    true = beq_nat n p.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_eq in eq1.
  inversion eq1.
  apply eq2.
Qed.

Theorem override_permute :
  forall {X:Type} x1 x2 k1 k2 k3 (f : nat -> X),
    false = beq_nat k2 k1 ->
    (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
  intros X x1 x2 k1 k2 k3 f eq1.
  unfold override.
  remember (beq_nat k1 k3) as bk1k3.
  destruct bk1k3.
  Case "bk1k3=true".
  apply beq_nat_eq in Heqbk1k3.
  rewrite <- Heqbk1k3.
  rewrite <- eq1.
  reflexivity.
  Case "bk1k3=false".
  reflexivity.
Qed.

Definition fold_length {X : Type} (l : list X) : nat:=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof.
  reflexivity.
Qed.

Theorem fold_length_correct:
  forall X (l : list X), fold_length l = length l.
Proof.
  intros X l.
  unfold fold_length.
  induction l as [|l0 l'].
  Case "l=[]".
  simpl.
  reflexivity.
  Case "l=l0:l'".
  simpl.
  apply eq_remove_S.
  apply IHl'.
Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l:list X) : list Y :=
  fold (fun x l => [f x] ++ l) l [].

Eval compute in fold_map (fun x => x * 2) [4,7,0].

Example test_fold_map : fold_map (fun x => x * 2) [4,7,0] = [8,14,0].
Proof.
  reflexivity.
Qed.

Theorem fold_map_corrent:
  forall X Y (f:X->Y) (l : list X), fold_map f l = map f l.
Proof.
  intros X Y f l.
  unfold fold_map.
  induction l as [|l0 l'].
  Case "l=[]".
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHl'.
  reflexivity.
Qed.

