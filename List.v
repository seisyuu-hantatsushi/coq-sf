Require Export Basic.

Module NatList.
  Inductive natprod: Type :=
    pair : nat -> nat -> natprod.

  Definition fst (p : natprod) : nat :=
    match p with
      | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
      | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Eval simpl in (fst (3,4)).

  Definition fst' (p : natprod) : nat :=
    match p with
      | (x,y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
      | (x,y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
      | (x,y) => (y,x)
    end.

  Theorem surjective_paring' :
    forall (n m:nat), (n,m) = (fst(n,m),snd(n,m)).
  Proof.
    intros n m.
    reflexivity.
  Qed.

  Theorem surjective_pairing_stuck :
    forall (p : natprod), p = (fst p, snd p).
  Proof.
    simpl. (* なにも変わらない！ *)
  Admitted.

  Theorem surjective_pairing :
    forall (p : natprod), p = (fst p, snd p).
  Proof.
    intros p.
    destruct p as (n,m).
    simpl.
    reflexivity.
  Qed.

  Theorem snd_fst_is_swap :
    forall (p : natprod), (snd p, fst p) = swap_pair p.
  Proof.
    intros p.
    destruct p as (n,m).
    simpl.
    reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

  Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

  Definition l_123'   := 1 :: (2 :: (3 :: nil)).
  Definition l_123''  := 1 :: 2 :: 3 :: nil.
  Definition l_123''' := [1,2,3].

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
      | O => nil
      | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l:natlist) : nat :=
    match l with
      | nil => O
      | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist): natlist:=
    match l1 with
      | nil => l2
      | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y)
                         (right associativity, at level 60).
  Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
  Proof.
    reflexivity.
  Qed.
  Example test_app2: nil ++ [4,5] = [4,5].
  Proof.
    reflexivity.
  Qed.
  Example test_app3: [1,2,3] ++ nil = [1,2,3].
  Proof.
    reflexivity.
  Qed.

  Definition hd (default:nat) (l:natlist) : nat :=
    match l with
      | nil => default
      | h :: t => h
    end.

  Definition tail (l:natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => t
    end.

  Example test_hd1: hd 0 [1,2,3] = 1.
  Proof.
    reflexivity.
  Qed.

  Example test_hd2: hd 0 [] = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_tail: tail [1,2,3] = [2,3].
  Proof.
    reflexivity.
  Qed.

  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
      | nil => nil
      | h::t => match h with
                  | 0 => nonzeros t
                  | _ => [h] ++ nonzeros t
                end
    end.
    
  Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
  Proof.
    reflexivity.
  Qed.

  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
      | nil => nil
      | h::t => match (oddb h) with
                  | true  => [h] ++ oddmembers t
                  | false => oddmembers t
                end
    end.

  Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
  Proof.
    reflexivity.
  Qed.

  Fixpoint countoddmembers (l:natlist): nat :=
    match l with
      | nil => 0
      | h::t => match (oddb h) with
                  | true  => 1 + countoddmembers t
                  | false =>  countoddmembers t
                end
    end.

  Example test_countoddmembers1: countoddmembers [1, 0, 3, 1, 4, 5] = 4.
  Proof.
    reflexivity.
  Qed.

  Example test_countoddmembers2: countoddmembers [0, 2, 4] = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_countoddmembers3: countoddmembers nil = 0.
  Proof.
    reflexivity.
  Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1,l2 with
      | nil, nil => nil
      | _,   nil => l1
      | nil, _   => l2
      | h1::t1,h2::t2 => [h1,h2] ++ alternate t1 t2
    end.

  Example test_alternate1 : alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate2 : alternate [1] [4,5,6] = [1,4,5,6].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate3 : alternate [1,2,3] [4] = [1,4,2,3].
  Proof.
    reflexivity.
  Qed.

  Example test_alternate4 : alternate [] [20,30] = [20,30].
  Proof.
    reflexivity.
  Qed.

  Definition bag := natlist.
  
  Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
      | nil => 0
      | sh::st => match beq_nat sh v with
                    | true  => 1 + count v st
                    | false => count v st
                  end
    end.
  
  Example test_count1: count 1 [1,2,3,1,4,1] = 3.
  Proof.
    reflexivity.
  Qed.

  Example test_count2: count 6 [1,2,3,1,4,1] = 0.
  Proof.
    reflexivity.
  Qed.

  Definition sum : bag -> bag -> bag :=
    alternate.

  Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Definition add (v:nat) (s:bag) : bag :=
    [v] ++ s.
  	
  Example test_add1: count 1 (add 1 [1,4,1]) = 3.
  Proof.
    reflexivity.
  Qed.

  Example test_add2: count 5 (add 1 [1,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Definition member (v:nat) (s:bag) : bool :=
    match (count v s) with
      | 0 => false
      | _ => true
    end.

  Example test_member1: member 1 [1,4,1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_member2: member 2 [1,4,1] = false.
  Proof.
    reflexivity.
  Qed.

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
      | nil => s
      | sh::st => if (beq_nat v sh) then st
                  else [sh] ++ remove_one v st
    end.

  Eval simpl in remove_one 5 [2,1,5,4,1].
  
  Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_one4: count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
  Proof.
    reflexivity.
  Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    if beq_nat (count v s) 0
    then s
    else match s with
           | nil => s
           | sh::st => if (beq_nat sh v)
                       then remove_all v st
                       else [sh] ++ remove_all v st
         end.
  
  Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
  Proof.
    reflexivity.
  Qed.

  Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
  Proof.
    reflexivity.
  Qed.

  Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
      | nil => true
      | s1_h::s1_t => if (member s1_h s2)
                      then subset s1_t (remove_one s1_h s2)
                      else false
    end.

  Example test_subset1: subset [1,2] [2,1,4,1] = true.
  Proof.
    reflexivity.
  Qed.

  Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
  Proof.
    reflexivity.
  Qed.

  Theorem nil_app:
    forall l:natlist, [] ++ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem tl_length_pred:
    forall l:natlist, pred (length l) = length (tail l).
  Proof.
    intros l.
    destruct l as [|n l'].
    Case "l = nil".
    reflexivity.
    Case "l = cons n l'".
    reflexivity.
  Qed.

  Theorem app_assoc:
    forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3.
    induction l1 as [| n l1'].
    Case "l1 = nil".
    reflexivity.
    Case "l1 = cons n l1'".
    simpl. rewrite->IHl1'.
    reflexivity.
  Qed.

  Theorem app_length:
    forall l1 l2 : natlist, length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l1'].
    Case "l1 = nil".
    reflexivity.
    Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'.
    reflexivity.
  Qed.

  Fixpoint snoc (l:natlist) (v:nat) : natlist :=
    match l with
      | nil => [v]
      | h :: t => h :: (snoc t v)
    end.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => snoc (rev t) h
    end.

  Example test_rev1: rev [1,2,3] = [3,2,1].
  Proof. reflexivity. Qed.

  Example test_rev2: rev nil = rev nil.
  Proof. reflexivity. Qed.

  Theorem length_snoc:
    forall n:nat, forall l:natlist, length (snoc l n) = S (length l).
  Proof.
    intros n l. induction l as [| n' l'].
    Case "l = []".
    reflexivity.
    Case "l=n::l'".
    simpl. rewrite -> IHl'. reflexivity.
  Qed.
    
  Theorem rev_length:
    forall l : natlist, length (rev l) = length l.
  Proof.
    intros l. induction l as [| n l'].
    Case "l = []".
    reflexivity.
    Case "l = n::l'".
    simpl.
    rewrite -> length_snoc.
    rewrite <- IHl'.
    reflexivity.
  Qed.

  Theorem app_nil_end:
    forall l:natlist,l++[]=l.
  Proof.
    intros l.
    induction l as [| n l'].
    Case "l=[]".
    simpl.
    reflexivity.
    Case "l=n::l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
  Qed.
  
  Theorem rev_involutive:
    forall l : natlist, rev (rev l) = l.
  Proof.    intros l. induction l as [| n l'].
    Case "l=[]".
    simpl.
    reflexivity.
    Case "l=n::l'".
    assert (H1: forall n:nat, forall l, rev (snoc l n) = n::rev l).
    intros n0 l.
    induction l as [| n0' l0'].
    SCase "l0'=[]".
    simpl.
    reflexivity.
    SCase "l0'=n0':l0''".
    simpl.
    rewrite -> IHl0'.
    simpl.
    reflexivity.
    simpl.
    rewrite->H1.
    rewrite->IHl'.
    reflexivity.
  Qed.

  Theorem app_ass4:
    forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_assoc.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

  Theorem scon_append:
    forall l:natlist, forall n:nat, snoc l n = l ++ [n].
  Proof.
    intros l n.
    induction l as [| n0 l'].
    Case "l=[]".
    simpl.
    reflexivity.
    Case "l=n::l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
  Qed.
  
  Theorem distr_rev :
    forall l1 l2:natlist, rev(l1++l2) = (rev l2) ++ (rev l1).
  Proof.
    intros l1 l2.
    induction l1 as [|n1 l1'].
    Case "l1=[]".
    simpl.
    rewrite -> app_nil_end.
    reflexivity.
    Case "l1=n1::l1'".
    simpl.
    rewrite -> IHl1'.
    rewrite -> scon_append.
    rewrite -> scon_append.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

  Theorem nonzeros_length:
    forall l1 l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2.
    induction l1 as [|n1 l1'].
    Case "l1=[]".
    simpl.
    reflexivity.
    Case "l1=n1::l1'".
    simpl.
    rewrite -> IHl1'.
    destruct n1.
    SCase "n1=0".
    reflexivity.
    SCase "n1=S".
    simpl.
    reflexivity.
  Qed.

  Theorem count_member_nonzero :
    forall (s: bag), ble_nat 1 (count 1 (1::s)) = true.
  Proof.
    intros s.
    simpl.
    reflexivity.
  Qed.

  Theorem ble_n_Sn:
    forall n, ble_nat n (S n) = true.
  Proof.
    intros n.
    induction n as [| n'].
    Case "n = 0".
    simpl.
    reflexivity.
    Case "n = S n".
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.

  Theorem remove_descrease_count:
    forall (s:bag), ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    intros s.
    induction s as [| s'].
    Case "s=0".
    simpl.
    reflexivity.
    Case "s = S n".
    simpl.
    destruct s'.
    SCase "s'=0".
    simpl.
    rewrite -> ble_n_Sn.
    reflexivity.
    SCase "s' = S s'".
    simpl.
    rewrite->IHs.
    reflexivity.
  Qed.

  Theorem rev_injective:
    forall l1 l2:natlist, rev l1 = rev l2 -> l1 = l2.
    intros.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint index (n:nat) (l:natlist) : natoption :=
    match l with
      | nil => None
      | a :: l' => match beq_nat n 0 with
                     | true => Some a
                     | false => index (pred n) l'
                   end
    end.

  Example test_index1 : index 0 [4,5,6,7] = Some 4.
  Proof.
    reflexivity.
  Qed.

  Example test_index2 : index 3 [4,5,6,7] = Some 7.
  Proof.
    reflexivity.
  Qed.

  Example test_index3 : index 10 [4,5,6,7] = None.
  Proof.
    reflexivity.
  Qed.

  Fixpoint index' (n:nat) (l:natlist) : natoption :=
    match l with
      | nil => None
      | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
    end.

  Definition option_elim (o:natoption) (d:nat) :nat :=
    match o with
      | Some n' => n'
      | None => d
    end.

  Definition hd_opt (l:natlist) : natoption :=
    match l with
      | nil => None
      | h::t => Some h
    end.

  Example test_hd_opt1 : hd_opt [] = None.
  Proof.
    reflexivity.
  Qed.

  Example test_hd_opt2 : hd_opt [1] = Some 1.
  Proof.
    reflexivity.
  Qed.

  Example test_hd_opt3 : hd_opt [5,6] = Some 5.
  Proof.
    reflexivity.
  Qed.

  Theorem option_elim_hd :
    forall (l:natlist) (default:nat),
      hd default l = option_elim (hd_opt l) default.
  Proof.
    intros.
    induction l as [| n l'].
    Case "l=[]".
    simpl.
    reflexivity.
    Case "l=n::l".
    simpl.
    reflexivity.
  Qed.
    
  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1 with
      | nil => match l2 with
                 | nil => true
                 | h::t => false
               end
      | h1::t1 => match l2 with
                    | nil => false
                    | h2::t2 => if beq_nat h1 h2 then beq_natlist t1 t2 else false
                  end
    end.

  Example test_beq_natlist1 : (beq_natlist nil nil = true).
  Proof.
    reflexivity.
  Qed.

  Example test_beq_natlist2 : (beq_natlist [1,2,3] [1,2,3] = true).
  Proof.
    reflexivity.
  Qed.

  Example test_beq_natlist3 : (beq_natlist [1,2,3] [1,2,4] = false).
  Proof.
    reflexivity.
  Qed.

  Theorem beq_natlist_refl:
    forall l:natlist, true = beq_natlist l l.
    intros l.
    induction l as [|n l'].
    Case "l=[]".
    reflexivity.
    Case "l=n::l'".
    simpl.
    rewrite <- beq_nat_refl.
    rewrite -> IHl'.
    reflexivity.
  Qed.

  Theorem silly1 :
    forall (n m o p : nat),
      n = m ->
      [n,o] = [n,p] ->
      [n,o] = [m,p].
  Proof.
    intros n m o p eq1 eq2.
    rewrite <- eq1.
    apply eq2.
  Qed.

  Theorem silly2 :
    forall (n m o p : nat),
      n = m ->
      (forall (q r : nat),  q = r -> [q,o]=[r,p]) ->
      [n,o] = [m,p].
  Proof.
    intros n m o p eq1 eq2.
    apply eq2.
    apply eq1.
  Qed.

  Theorem silly2':
    forall (n m o p : nat),
      n = m ->
      (forall (q r : nat),  q = r -> [q,o]=[r,p]) ->
      [n,o] = [m,p].
  Proof.
    intros.
  Admitted.

  Theorem silly2a:
    forall (n m : nat),
      (n,n) = (m,m) ->
      (forall (q r : nat),  (q,q) = (r,r) -> [q]=[r]) ->
      [n] = [m].
  Proof.
    intros n m eq1 eq2.
    apply eq2.
    apply eq1.
  Qed.

  Theorem silly_ex:
    (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true ->
    oddb 4 = true.
  Proof.
    intros.
    apply H.
    apply H0.
  Qed.

  Theorem silly3:
    forall (n:nat),
      true = beq_nat n 5 ->
      beq_nat (S (S n)) 7 = true.
  Proof.
    intros.
    symmetry.
    apply H.
  Qed.

  Theorem rev_exercise1:
    forall (l l' : natlist), l = rev l' -> l' = rev l.
  Proof.
    intros.
    rewrite -> H.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Theorem app_ass':
    forall (l1 l2 l3 : natlist), (l1++l2)++l3=l1++(l2++l3).
  Proof.
    intros l1.
    induction l1 as [| n l1'].
    Case "l1 = []".
    simpl.
    reflexivity.
    Case "l1=n::l1'".
    intros.
    simpl.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

  Theorem beq_nat_sym :
    forall (n m : nat), beq_nat n m = beq_nat m n.
  Proof.
    intros n.
    induction n as [| n'].
    Case "n=0".
    simpl.
    intros.
    destruct m as [m1 | m2].
    SCase "m=0".
    simpl.
    reflexivity.
    SCase "m=S m".
    simpl.
    reflexivity.
    Case "n=S n".
    intros.
    simpl.
    destruct m as [m1 | m2].
    SCase "m=0".
    simpl.
    reflexivity.
    SCase "m = S m".
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.

End NatList.

Module Dictionary.

  Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

  Definition insert (key value : nat) (d : dictionary) : dictionary :=
    (record key value d).

  Fixpoint find (key : nat) (d: dictionary) : option nat :=
    match d with
      | empty => None
      | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
    end.

  Theorem dictionary_invariant1 :
    forall (d: dictionary) (k v:nat), (find k (insert k v d)) = Some v.
  Proof.
    assert(H:forall (k:nat), beq_nat k k = true).
    intros.
    induction k as [|k'].
    Case "k=0".
    simpl.
    reflexivity.
    Case "k=S k'".
    simpl.
    rewrite -> IHk'.
    reflexivity.
    simpl.
    intros d k.
    rewrite -> H.
    reflexivity.
  Qed.

  Theorem dictionary_invariant2 :
    forall (d:dictionary) (m n o:nat),
      (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
  Proof.
    intros.
    simpl.
    rewrite -> H.
    reflexivity.
  Qed.

End Dictionary.

Definition beq_nat_sym := NatList.beq_nat_sym.
