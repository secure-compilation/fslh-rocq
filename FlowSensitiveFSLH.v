(** * Flow-Sensitive, Flexible Value SLH *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps SpecCT UltimateSLH_optimized FlexSLH FlexVSLH.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

(** * Flow-sensitive IFC tracking for flex_slh *)

(* Since we want to apply flex_slh to all programs, without rejecting anything
   as "ill-typed", we implement flow-sensitive static IFC tracking: *)

Inductive acom : Type :=
  | ASkip
  | AAsgn (x : string) (e : aexp)
  | ASeq (c1 c2 : acom)
  | AIf (be : bexp) (lbe : label) (c1 c2 : acom)
  | AWhile (be : bexp) (lbe : label) (c : acom)
  | AARead (x : string) (lx : label) (a : string) (i : aexp)  (li : label)
  | AAWrite (a : string) (i : aexp) (li : label) (e : aexp).

Declare Custom Entry acom.

Notation "'<[' e ']>'" := e (at level 0, e custom acom at level 99) : com_scope.
Notation "( x )" := x (in custom acom, x at level 99) : com_scope.
Notation "x" := x (in custom acom at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom acom at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Notation "'skip'"  :=
  ASkip (in custom acom at level 0) : com_scope.
Notation "x := y"  :=
  (AAsgn x y)
    (in custom acom at level 0, x constr at level 0,
      y custom acom at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (ASeq x y)
    (in custom acom at level 90, right associativity) : com_scope.
Notation "'if' x '@' lbe 'then' y 'else' z 'end'" :=
  (AIf x lbe y z)
    (in custom acom at level 89, x custom acom at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x '@' lbe 'do' y 'end'" :=
  (AWhile x lbe y)
    (in custom acom at level 89, x custom acom at level 99, y at level 99) : com_scope.
Notation "x '@@' lx '<-' a '[[' i '@' li ']]'"  :=
  (AARead x lx a i li)
     (in custom acom at level 0, x constr at level 0,
      a at level 85, i custom acom at level 85, no associativity) : com_scope.
Notation "a '[' i '@' li  ']'  '<-' e"  :=
  (AAWrite a i li e)
     (in custom acom at level 0, a constr at level 0,
      i custom acom at level 0, e custom acom at level 85,
         no associativity) : com_scope.

Fixpoint erase (ac:acom) : com :=
  match ac with
  | <[ skip ]> => <{skip}>
  | <[ X := ae ]> => <{X := ae}>
  | <[ ac1 ; ac2 ]> => <{ erase ac1; erase ac2 }>
  | <[ if be@lbe then ac1 else ac2 end ]> => <{ if be then erase ac1
                                                      else erase ac2 end }>
  | <[ while be @ lbe do ac1 end ]> => <{ while be do erase ac1 end }>
  | <[ X@@lx <- a[[i@li]] ]> => <{ X <- a[[i]] }>
  | <[ a[i@li] <- e ]> => <{ a[i] <- e }>
  end.

Definition join_pub_vars (P1 P2: pub_vars) : pub_vars :=
  fun x => join (P1 x) (P2 x).

Definition str_nodup := nodup string_dec.

Fixpoint assigned_vars c :=
  match c with
  | <{ skip }> | <{ _ [_] <- _ }> => []
  | <{ X := _ }> | <{ X <- _ [[_]] }> => [X]
  | <{ c1; c2 }>
  | <{ if _ then c1 else c2 end }> => str_nodup (assigned_vars c1 ++ assigned_vars c2)
  | <{ while _ do c end }> => assigned_vars c
  end.

Fixpoint assigned_arrs c :=
  match c with
  | <{ skip }>
  | <{ _ := _ }>
  | <{ _ <- _ [[_]] }> => []
  | <{ c1; c2 }>
  | <{ if _ then c1 else c2 end }> => str_nodup (assigned_arrs c1 ++ assigned_arrs c2)
  | <{ while _ do c end }> => assigned_arrs c
  | <{ a[_] <- _ }> => [a]
  end.

Definition list_eqb l1 l2 := if list_eq_dec string_dec l1 l2 then true else false.

Fixpoint static_tracking_while (static_tracking : pub_vars -> pub_arrs -> label -> (acom * pub_vars * pub_arrs))
      (P : pub_vars) (PA : pub_arrs) (pc : label) (i : nat) (be : bexp) (vars arrs pvars parrs : list string) :=
  let lbe := label_of_bexp P be in
  let '(ac, P1, PA1) := static_tracking P PA (join pc lbe) in
  let P1 := join_pub_vars P P1 in
  let PA1 := join_pub_vars PA PA1 in
  let pvars1 := filter P1 vars in
  let parrs1 := filter PA1 arrs in
  let stop := (list_eqb pvars pvars1) && (list_eqb parrs parrs1) in
    (* Stopping if a fixpoint was already reached *)
  match i, stop with
  | _, true | 0, _ => (P1, PA1, lbe, ac)
  | S i, false => static_tracking_while static_tracking P1 PA1 pc i be vars arrs pvars1 parrs1
  end.

Fixpoint static_tracking (c:com) (P:pub_vars) (PA:pub_arrs) (pc:label)
  : (acom*pub_vars*pub_arrs) :=
  match c with
  | <{ skip }> => (<[skip]>, P, PA)
  | <{ X := ae }> => (<[X := ae]>, X !-> (join pc (label_of_aexp P ae)); P, PA)
  | <{ c1; c2 }> => let '(ac1, P1, PA1) := static_tracking c1 P PA pc in
                    let '(ac2, P2, PA2) := static_tracking c2 P1 PA1 pc in
                     (<[ ac1; ac2 ]>, P2, PA2)
  | <{ if be then c1 else c2 end }> =>
      let lbe := label_of_bexp P be in
      let '(ac1, P1, PA1) := static_tracking c1 P PA (join pc lbe) in
      let '(ac2, P2, PA2) := static_tracking c2 P PA (join pc lbe) in
      (<[ if be@lbe then ac1 else ac2 end ]>, join_pub_vars P1 P2, join_pub_vars PA1 PA2)
  | <{ while be do c1 end }> =>
      let vars := assigned_vars c1 in
      let arrs := assigned_arrs c1 in
      let pvars := filter P vars in
      let parrs := filter PA arrs in
      let max_iters := length vars + length arrs in
      let '(P', PA', lbe, ac1) := static_tracking_while (static_tracking c1) P PA pc max_iters be vars arrs pvars parrs in
      (<[ while be@lbe do ac1 end ]>, P', PA')
  | <{ X <- a[[i]] }> =>
      let li := label_of_aexp P i in
      let lx := join pc (join li (PA a)) in
      (<[ X@@lx <- a[[i@li]] ]>, X !-> lx; P, PA)
  | <{ a[i] <- e }> =>
      let li := label_of_aexp P i in
      let la := join (PA a) (join pc (join li (label_of_aexp P e))) in
      (* It seems likely that the arrays will all become private quite quickly *)
      (<[ a[i@li] <- e ]>, P, a !-> la; PA)
  end.

Lemma erase_static_tracking_while : forall f P PA pc i be vars arrs pvars parrs c,
  (forall P PA pc, let '(ac', _, _) := f P PA pc in erase ac' = c) ->
  let '(_, _, _, ac) := static_tracking_while f P PA pc i be vars arrs pvars parrs in
  erase ac = c.
Proof.
  intros until i. revert f P PA pc. induction i; simpl; intros.
  + specialize (H P PA (join pc (label_of_bexp P be))).
    destruct (f P PA (join pc (label_of_bexp P be))) as ((ac&P1)&PA1).
    now destruct (list_eqb pvars (filter (join_pub_vars P P1) vars) && list_eqb parrs (filter (join_pub_vars PA PA1) arrs)).
  + destruct (f P PA (join pc (label_of_bexp P be))) as ((ac&P1)&PA1) eqn:Heq.
    specialize (H P PA (join pc (label_of_bexp P be))) as H'. rewrite Heq in H'. clear Heq.
    destruct (list_eqb pvars (filter (join_pub_vars P P1) vars) && list_eqb parrs (filter (join_pub_vars PA PA1) arrs)); [assumption|].
    now apply IHi.
Qed.

Lemma erase_static_tracking : forall c P PA pc,
  let '(ac, _, _) := static_tracking c P PA pc in
  erase ac = c.
Proof.
  induction c; simpl; auto; intros.
  + specialize (IHc1 P PA pc).
    destruct (static_tracking c1 P PA pc) as ((ac&P1)&PA1).
    specialize (IHc2 P1 PA1 pc).
    destruct (static_tracking c2 P1 PA1 pc) as ((ac'&P2)&PA2).
    simpl. congruence.
  + specialize (IHc1 P PA (join pc (label_of_bexp P be))).
    specialize (IHc2 P PA (join pc (label_of_bexp P be))).
    destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac&P1)&PA1).
    destruct (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac'&P2)&PA2).
    simpl. congruence.
  + destruct (static_tracking_while (static_tracking c) P PA pc (Datatypes.length (assigned_vars c) + Datatypes.length (assigned_arrs c)) be (assigned_vars c)
      (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c))) as (((P1&PA1)&pc1)&ac) eqn:Heq.
    eapply erase_static_tracking_while in IHc. erewrite Heq in IHc. simpl. congruence.
Qed.

Fixpoint flex_vslh_acom ac :=
  match ac with
  | <[ skip ]> => <{ skip }>
  | <[ X := ae ]> => <{ X := ae }>
  | <[ ac1; ac2 ]> => <{ flex_vslh_acom ac1; flex_vslh_acom ac2 }>
  | <[ if be@lbe then ac1 else ac2 end ]> =>
      let be' := if lbe then be else <{ "b" = 0 && be }> in
      <{ if be' then "b" := be' ? "b" : 1; flex_vslh_acom ac1 else
                     "b" := be' ? 1 : "b"; flex_vslh_acom ac2 end }>
  | <[ while be@lbe do ac end ]> =>
      let be' := if lbe then be else <{ "b" = 0 && be }> in
      <{ while be' do "b" := be' ? "b" : 1; flex_vslh_acom ac end; "b" := be' ? 1 : "b" }>
  | <[ X@@lx <- a[[i@li]] ]> =>
      let i' := if li && negb lx then i else <{ ("b" = 1) ? 0 : i }> in
      if lx && li then <{ X <- a[[i]]; X := ("b" = 1) ? 0 : X }> else <{ X <- a[[i']] }>
  | <[ a[i@li] <- e ]> => let i' := if li then i else <{ ("b" = 1) ? 0 : i }> in
      <{ a[i'] <- e }>
  end.

Definition fs_flex_vslh P PA c :=
  let '(ac, _, _) := static_tracking c P PA public in
  flex_vslh_acom ac.

(** * Ideal small-step evaluation *)

Reserved Notation
  "'<[[' c , st , ast , b ']]>' '-->i_' ds '^^' os '<[[' ct , stt , astt , bt ']]>'"
  (at level 40, c custom acom at level 99, ct custom acom at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    acom -> state -> astate -> bool ->
    acom -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn : forall X ae n st ast b,
      aeval st ae = n ->
      <[[X := ae, st, ast, b]]> -->i_[]^^[] <[[skip, X !-> n; st, ast, b]]>
  | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2,
      <[[c1, st, ast, b]]>  -->i_ds^^os <[[c1t, stt, astt, bt]]>  ->
      <[[(c1;c2), st, ast, b]]>  -->i_ds^^os <[[(c1t;c2), stt, astt, bt]]>
  | ISM_Seq_Skip : forall st ast b c2,
      <[[(skip;c2), st, ast, b]]>  -->i_[]^^[] <[[c2, st, ast, b]]>
  | ISM_If : forall be ct cf st ast b c' b' lbe,
      b' = (lbe || negb b) && beval st be ->
      c' = (if b' then ct else cf) ->
      <[[if be@lbe then ct else cf end, st, ast, b]]> -->i_[DStep]^^[OBranch b'] <[[c', st, ast, b]]>
  | ISM_If_F : forall be ct cf st ast b c' b' lbe,
      b' = (lbe || negb b) && beval st be ->
      c' = (if b' then cf else ct) ->
      <[[if be@lbe then ct else cf end, st, ast, b]]> -->i_[DForce]^^[OBranch b'] <[[c', st, ast, true]]>
  | ISM_While : forall be c st ast b lbe c',
      c' = <[ if be@lbe then c; while be@lbe do c end else skip end ]> ->
      <[[while be@lbe do c end, st, ast, b]]> -->i_[]^^[] <[[c', st, ast, b]]>
  | ISM_ARead : forall X a ie st ast (b :bool) i li lX v,
      (if (negb li) && b then 0 else (aeval st ie)) = i ->
      (if lX && li && b then 0 else nth i (ast a) 0) = v ->
      i < length (ast a) ->
      <[[X@@lX <- a[[ie@li]], st, ast, b]]> -->i_[DStep]^^[OARead a i]
            <[[skip, X !-> v; st, ast, b]]>
  | ISM_ARead_U : forall X a ie st ast i a' i' v (lX:label),
      aeval st ie = i ->
      v = (if lX then 0 else nth i' (ast a') 0) ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <[[X@@lX <- a[[ie@public]], st, ast, true]]> -->i_[DLoad a' i']^^[OARead a i]
            <[[skip, X !-> v; st, ast, true]]>
  | ISM_Write : forall a ie e st ast (b :bool) i n li i',
      aeval st e = n ->
      aeval st ie = i ->
      (if b && negb li then 0 else i) = i' ->
      i' < length (ast a) ->
      <[[a[ie@li] <- e, st, ast, b]]> -->i_[DStep]^^[OAWrite a i']
            <[[skip, st, a !-> upd i' (ast a) n; ast, b]]>
  | ISM_Write_U : forall a ie e st ast i n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <[[a[ie@public] <- e, st, ast, true]]> -->i_[DStore a' i']^^[OAWrite a i]
            <[[skip, st, a' !-> upd i' (ast a') n; ast, true]]>

  where "<[[ c , st , ast , b ]]> -->i_ ds ^^ os  <[[ ct ,  stt , astt , bt ]]>" :=
    (ideal_eval_small_step c st ast b ct stt astt bt ds os).

Reserved Notation
  "'<[[' c , st , ast , b ']]>' '-->i*_' ds '^^' os '<[[' ct , stt , astt , bt ']]>'"
  (at level 40, c custom acom at level 99, ct custom acom at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (c:acom) (st:state) (ast:astate) (b:bool) :
    acom -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_ideal_refl : <[[c, st, ast, b]]> -->i*_[]^^[] <[[c, st, ast, b]]>
  | multi_ideal_trans (c':acom) (st':state) (ast':astate) (b':bool)
                (c'':acom) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      <[[c, st, ast, b]]> -->i_ds1^^os1 <[[c', st', ast', b']]> ->
      <[[c', st', ast', b']]> -->i*_ds2^^os2 <[[c'', st'', ast'', b'']]> ->
      <[[c, st, ast, b]]> -->i*_(ds1++ds2)^^(os1++os2) <[[c'', st'', ast'', b'']]>

  where "<[[ c , st , ast , b ]]> -->i*_ ds ^^ os  <[[ ct ,  stt , astt , bt ]]>" :=
    (multi_ideal c st ast b ct stt astt bt ds os).

Definition ideal_same_obs ac st1 st2 ast1 ast2 :=
  forall ds os1 os2 stt1 stt2 astt1 astt2 ac1 ac2 b1 b2,
    <[[ac, st1, ast1, false]]> -->i*_ds^^os1 <[[ac1, stt1, astt1, b1]]> ->
    <[[ac, st2, ast2, false]]> -->i*_ds^^os2 <[[ac2, stt2, astt2, b2]]> ->
    os1 = os2.

Lemma multi_ideal_trans_nil_l c st ast b c' st' ast' b' ct stt astt bt ds os :
  <[[c, st, ast, b]]> -->i_[]^^[] <[[c', st', ast', b']]> ->
  <[[c', st', ast', b']]> -->i*_ds^^os <[[ct, stt, astt, bt]]> ->
  <[[c, st, ast, b]]> -->i*_ds^^os <[[ct, stt, astt, bt]]>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_trans_nil_r c st ast b c' st' ast' b' ct stt astt bt ds os :
  <[[c, st, ast, b]]> -->i_ds^^os <[[c', st', ast', b']]> ->
  <[[c', st', ast', b']]> -->i*_[]^^[] <[[ct, stt, astt, bt]]> ->
  <[[c, st, ast, b]]> -->i*_ds^^os <[[ct, stt, astt, bt]]>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_combined_executions :
  forall c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost,
    <[[c, st, ast, b]]> -->i*_ds^^osm <[[cm, stm, astm, bm]]> ->
    <[[cm, stm, astm, bm]]> -->i*_dsm^^ost <[[ct, stt, astt, bt]]> ->
    <[[c, st, ast, b]]> -->i*_(ds++dsm)^^(osm++ost) <[[ct, stt, astt, bt]]>.
Proof.
  intros c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost Hev1 Hev2.
  induction Hev1.
  - do 2 rewrite app_nil_l. apply Hev2.
  - do 2 rewrite <- app_assoc. eapply multi_ideal_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

Lemma multi_ideal_add_snd_com : forall c st ast ct stt astt ds os c2 b bt,
  <[[c, st, ast, b]]> -->i*_ds^^os <[[ct, stt, astt, bt]]> ->
  <[[c;c2, st, ast, b]]> -->i*_ds^^os <[[ct;c2, stt, astt, bt]]>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Definition acom_unused X ac := unused X (erase ac).

Fixpoint acom_size (c :acom) :nat :=
  match c with
  | <[ c1; c2 ]> => 1 + (acom_size c1) + (acom_size c2)
  (* For conditionals the maximum of both branches is tighter, but a
     looser bound based on blindly "counting all constructors"
     (commented here) works just as well, and is easier to explain on
     paper *)
  | <[ if _@_ then ct else cf end ]> => 1 + max (acom_size ct) (acom_size cf)
  (* | <{{ if be then ct else cf end }}> => 1 + (com_size ct) + (com_size cf) *)
  | <[ while _@_ do cw end ]> => 1 + (acom_size cw)
  | _  => 1
  end.

Definition prog_size (c :acom) (ds :dirs) :nat := acom_size c + length ds.

(** The induction principle on [prog_size] *)

Lemma prog_size_ind :
  forall P : acom -> dirs -> Prop,
  (forall c ds,
    ( forall c' ds',
      prog_size c' ds' < prog_size c ds ->
      P c' ds') -> P c ds  ) ->
  (forall c ds, P c ds).
Proof.
  intros.
  remember (fun c_ds => P (fst c_ds) (snd c_ds)) as P'.
  replace (P c ds) with (P' (c, ds)) by now rewrite HeqP'.
  eapply measure_induction with (f:=fun c_ds => prog_size (fst c_ds) (snd c_ds)). intros. rewrite HeqP'.
  apply H. intros.
  remember (c', ds') as c_ds'.
  replace (P c' ds') with (P' c_ds') by now rewrite Heqc_ds', HeqP'.
  apply H0. now rewrite Heqc_ds'.
Qed.

(** The proof of [sel_slh_flag] *)

Lemma prog_size_monotonic: forall c1 ds1 c2 ds2,
  (acom_size c1 < acom_size c2 /\ length ds1 <= length ds2 ) \/
  (acom_size c1 <= acom_size c2 /\ length ds1 < length ds2) ->
  prog_size c1 ds1 < prog_size c2 ds2.
Proof.
  intros c1 ds1 c2 ds2 [ [Hcom Hdir] | [Hcom Hdir] ];
  unfold prog_size; lia.
Qed.

(** Based on the Lemma [prog_size_monotonic] we can build a tactic to solve
    the subgoals in the form of [prog_size c' ds' < prog_size c ds],
    which will be produced by [prog_size_ind].*)

Ltac prog_size_auto :=
  try ( apply prog_size_monotonic; left; split; simpl;
        [| repeat rewrite app_length]; lia );
  try ( apply prog_size_monotonic; right; split; simpl;
        [| repeat rewrite app_length]; lia);
  try ( apply prog_size_monotonic; left; split; simpl;
        [auto | repeat rewrite app_length; lia] ).

Ltac solve_refl :=
  now (do 2 eexists); split; [|split; [(try discriminate); (try now repeat econstructor)|(try discriminate); tauto] ]; rewrite ?t_update_shadow, t_update_same;
  repeat econstructor; (repeat rewrite_eq); rewrite ?andb_false_r; (try now apply label_of_exp_sound).

Lemma flex_slh_acom_bcc_generalized : forall ac st ast c' st' ast' os ds (b b' : bool),
  nonempty_arrs ast ->
  acom_unused "b" ac ->
  st "b" = (if b then 1 else 0) ->
  <((flex_vslh_acom ac, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists st'' ac',
  <[[ac, st, ast, b]]> -->i*_ds^^os <[[ac', "b" !-> st "b"; st'', ast', b']]> /\
  (c' = <{{ skip }}> -> ac' = <[ skip ]> /\ st' "b" = (if b' then 1 else 0) /\ st' = st'').
Proof.
  intros until ds. revert st ast c' st' ast' os. eapply prog_size_ind with (c:=ac) (ds:=ds).
  clear. intros until b'. intros Harrs Hunused st_b Hexec. destruct c; simpl in *.
  + invert Hexec; [|inversion H0]. do 2 eexists. split; [|tauto]. rewrite t_update_same. constructor.
  + invert Hexec; [solve_refl|]. invert H0. invert H1; [|inversion H0]. do 2 eexists. rewrite t_update_neq; [|now invert Hunused]. split; [|tauto].
    rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same. now repeat econstructor.
  + apply multi_spec_seq in Hexec. destruct Hexec.
    - do 8 destruct H0. destruct H1, H2. subst. apply spec_eval_preserves_nonempty_arrs in H2 as ?; [|tauto].
      invert Hunused. apply H in H2; [|prog_size_auto|tauto..]. destruct H2 as (?&?&?&(->&?&->)); [tauto|].
      apply H in H3; [|prog_size_auto|tauto..]. destruct H3 as (?&?&?&?). do 2 eexists. split; [|apply H6].
      admit.
    - destruct H0 as (?&->&?). invert Hunused. apply H in H0; [|prog_size_auto|tauto..]. destruct H0 as (?&?&?&?).
      do 2 eexists. split; [|discriminate]. apply multi_ideal_add_snd_com. apply H0.
  + admit.
  + admit.
  + destruct (lx&&li) eqn:Heq.
    - apply andb_prop in Heq. destruct Heq. subst.
      invert Hexec; [solve_refl|]. invert H0. invert H13.
      * invert H1. { do 2 eexists. split; [|discriminate]. repeat econstructor; [tauto|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0; [inversion H13|]. invert H2. { do 2 eexists. split; [|discriminate]. rewrite app_nil_l. repeat econstructor; [tauto|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0. invert H1; [|inversion H0]. rewrite t_update_shadow. rewrite t_update_neq; [|now invert Hunused].
        do 2 eexists. split; [|tauto]. rewrite !app_nil_l. repeat econstructor; [tauto|]. simpl. rewrite t_update_neq; [|now invert Hunused].
        rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same, t_update_eq, st_b. now destruct b'; constructor.
      * invert H1. { do 2 eexists. split; [|discriminate]. repeat econstructor; [tauto..|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [|now invert Hunused]. constructor. }
        invert H0; [inversion H13|]. invert H2. { do 2 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; [tauto..|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0. invert H1; [|inversion H0]. rewrite t_update_shadow. rewrite t_update_neq; [|now invert Hunused].
        do 2 eexists. split; [|tauto]. rewrite !app_nil_l. repeat econstructor; [tauto..|]. rewrite t_update_permute; [|now invert Hunused].
        rewrite t_update_same. simpl. rewrite t_update_neq; [|now invert Hunused]. rewrite st_b. constructor.
    - invert Hexec; [solve_refl|]. invert H0.
      * invert H1; [|inversion H0]. rewrite t_update_neq; [|now invert Hunused]. do 2 eexists. split; [|tauto].
        repeat econstructor; [|tauto|]. { destruct lx, li, b'; simpl in *; rewrite ?st_b; try reflexivity; discriminate. }
        rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same. destruct li, lx, b'; simpl; rewrite ?st_b; try constructor; discriminate.
      * simpl in H15. invert H1; [|inversion H0]. admit.
  +
Admitted.

Lemma fs_flex_vsls_correct_small_step : forall P PA c c' st ast st' ast' os,
  st "b" = 0 ->
  unused "b" c ->
  <(( c, st, ast ))> -->^ os <((c', st', ast'))> ->
  exists c'',
  <((fs_flex_vslh P PA c, st, ast))> -->*^ os <((c'', st', ast'))> /\ (c' = <{ skip }> -> c'' = <{ skip }>).
Proof.
  intros until os. intros st_b Hunused H. revert Hunused. induction H; unfold fs_flex_vslh in *; simpl; intro Hunused.
  + eexists. split; [rewrite <- app_nil_l; repeat econstructor|reflexivity].
    rewrite H. constructor.
  + destruct IHseq_eval_small_step as (c''&?&?); [tauto..|]. destruct (static_tracking c1 P PA public) as ((ac&P1)&PA1) eqn:Heq.
    destruct (static_tracking c2 P1 PA1 public) as ((ac'&P2)&PA2) eqn:Heq'. simpl.
    eexists. split; [|discriminate]. apply multi_seq_add_snd_com, H0.
  + destruct (static_tracking c2 P PA public) as ((ac&P')&PA') eqn:Heq.
    eexists. simpl. change [] with ([] ++ [] : obs). split; [eapply multi_seq_trans; [apply SSM_Seq_Skip|constructor]|].
    intros ->. simpl in Heq. now invert Heq.
  + destruct (static_tracking ct P PA (label_of_bexp P be)) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking cf P PA (label_of_bexp P be)) as ((ac2&P2)&PA2) eqn:Heq2.
    simpl. destruct (label_of_bexp P be) eqn:Heq.
    - exists (if beval st be then flex_vslh_acom ac1 else flex_vslh_acom ac2).
      split; [|now destruct (beval st be); intros ->; [invert Heq1|invert Heq2] ].
      simpl. change [_] with ([OBranch (beval st be)] ++ [] ++ [] ++ []).
      econstructor; [constructor|]. destruct (beval st be) eqn:Hbe; (do 2 econstructor; [now constructor; simpl; rewrite Hbe|apply SSM_Seq_Skip|rewrite t_update_same; constructor]).
    - exists (if beval st be then flex_vslh_acom ac1 else flex_vslh_acom ac2).
      split; [|now destruct (beval st be); intros ->; [invert Heq1|invert Heq2] ].
      simpl. change [_] with ([OBranch (beval st be)] ++ [] ++ [] ++ []).
      replace (beval st be) with (beval st <{{ "b" = 0 && be }}>) by now (simpl; rewrite ?st_b).
      econstructor; [constructor|].
      destruct (beval st <{{ "b" = 0 && be }}>) eqn:Hbe; (do 2 econstructor; [now constructor; simpl in *; rewrite Hbe|apply SSM_Seq_Skip|rewrite t_update_same; constructor]).
  + destruct (static_tracking_while (static_tracking c) P PA public (length (assigned_vars c) + length (assigned_arrs c)) be (assigned_vars c) 
       (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c))) as (((?&?)&?)&?).
    eexists. split; [constructor|discriminate].
  + eexists. split; [|reflexivity]. destruct (join (label_of_aexp P ie) (PA a) && label_of_aexp P ie).
    - change [_] with ([OARead a i] ++ [] ++ [] ++ []).
      econstructor; [now repeat econstructor|]. econstructor; [apply SSM_Seq_Skip|]. econstructor; [|constructor].
      remember (x !-> _; st) as st'.
      replace st' with (x !-> aeval st' <{ ("b" = 1) ? 0 : x }>; st') at 2
        by now rewrite Heqst'; simpl; rewrite t_update_neq; [|tauto]; rewrite st_b, t_update_same.
      now constructor.
    - rewrite <- app_nil_r. repeat econstructor; [|tauto].
      now destruct (label_of_aexp P ie && negb (join (label_of_aexp P ie) (PA a))); simpl; rewrite ?st_b.
  + eexists. split; [|reflexivity].
    rewrite <- app_nil_r. repeat econstructor; [|tauto|rewrite H; constructor].
    now destruct (label_of_aexp P ie); simpl; rewrite ?st_b.
Qed.

Lemma seq_unused : forall X c st ast c' st' ast' os,
  <((c, st, ast))> -->^os <((c', st', ast'))> ->
  unused X c ->
  unused X c' /\ st' X = st X.
Proof.
  intros. revert H0. induction H; simpl; intro; rewrite ?t_update_neq; try tauto.
  destruct (beval st be); tauto.
Qed.

(* LD: This kind of theorem would be nice to have...
       The one step version isn't strong enough as it is stated though *)
Theorem fs_flex_vslh_correct : forall P PA c c' st ast st' ast' os,
  st "b" = 0 ->
  unused "b" c ->
  <(( c, st, ast ))> -->*^ os <((c', st', ast'))> ->
  exists c'',
  <((fs_flex_vslh P PA c, st, ast))> -->*^ os <((c'', st', ast'))>.
Proof.
Admitted.

(* LD: Add a way to know that ac comes is created from P PA for which the states are equivalent *)
(* CH: You could add something like this (and potentially use c instead of `erase ac`
       in the premise, although your theorems will probably anyway say it's all the same):
  static_tracking c P PA public = (ac, P', PA') ->
  pub_equiv P st st' ->
  pub_equiv PA ast ast' -> *)
It will probably be very similar to the main theorem statement below?
       In particular, can't you use fs_flex_vslh in the conclusion instead of erased in the premise? *)
Theorem ideal_eval_relative_secure : forall ac st st' ast ast',
  nonempty_arrs ast ->
  nonempty_arrs ast' ->
  seq_same_obs (erase ac) st st' ast ast' ->
  ideal_same_obs ac st st' ast ast'.
Proof.
Admitted.

(* LD: Does not rely on pub_equiv right now, probably something wrong in the other statements *)
(* CH: I agree that these pub_equiv conditions seem also needed above *)
Theorem fs_flex_vslh_relative_secure : forall P PA c st ast st' ast',
  unused "b" c ->
  st "b" = 0 ->
  st' "b" = 0 ->
  pub_equiv P st st' ->
  pub_equiv PA ast ast' ->
  nonempty_arrs ast ->
  nonempty_arrs ast' ->
  seq_same_obs c st st' ast ast' ->
  spec_same_obs (fs_flex_vslh P PA c) st st' ast ast'.
Proof.
  unfold spec_same_obs, fs_flex_vslh. intros.
  destruct (static_tracking c P PA public) as ((ac&P')&PA') eqn:Heq.
  pose proof (erase_static_tracking c P PA public). rewrite Heq in H9. subst.
  apply flex_slh_acom_bcc in H7; [|tauto..].
  apply flex_slh_acom_bcc in H8; [|tauto..].
  destruct H7, H8.
  eapply ideal_eval_relative_secure; [apply H4|apply H5|eassumption..].
Qed.

(* CH: My advice would be to also look at the 2 other conjectures I tested
   at the very end of TestingFlexSLH.v and turn that into noninterference and
   ideal_misspeculated_unwinding lemmas in the proofs. *)






































