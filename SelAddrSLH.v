(** * aSelSLH : Selective Address SLH *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps SpecCT UltimateSLH_optimized.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

Ltac rewrite_eq :=
  match goal with
  | H:_=_ |- _ => rewrite H; clear H
  | H:forall _, _=_ |- _ => rewrite H; clear H
  | _ => idtac
 end.

Fixpoint label_of_aexp (P:pub_vars) (a:aexp) : label :=
  match a with
  | ANum n => public
  | AId x => P x
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ be ? a1 : a2 }> => join (label_of_bexp P be) (join (label_of_aexp P a1) (label_of_aexp P a2))
  end
with label_of_bexp (P:pub_vars) (b:bexp) : label :=
  match b with
  | <{ true }> | <{ false }> => public
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ ~b }> => label_of_bexp P b
  | <{ b1 && b2 }> => join (label_of_bexp P b1) (label_of_bexp P b2)
  end.

Lemma label_of_exp_sound : forall P,
  (forall a, P |-a- a \in label_of_aexp P a) /\
  (forall b, P |-b- b \in label_of_bexp P b).
Proof. intro P. apply aexp_bexp_mutind; intros; now constructor. Qed.

Corollary label_of_aexp_sound : forall P a,
  P |-a- a \in label_of_aexp P a.
Proof. intros. apply label_of_exp_sound. Qed.

Corollary label_of_bexp_sound : forall P b,
  P |-b- b \in label_of_bexp P b.
Proof. intros. apply label_of_exp_sound. Qed.

Lemma label_of_exp_unique : forall P,
  (forall a l, P |-a- a \in l -> l = label_of_aexp P a) /\
  (forall b l, P |-b- b \in l -> l = label_of_bexp P b).
Proof. intro P. apply aexp_bexp_has_label_mutind; intros; (repeat rewrite_eq); reflexivity. Qed.

Corollary label_of_aexp_unique : forall P a l,
  P |-a- a \in l ->
  l = label_of_aexp P a.
Proof. intro. apply label_of_exp_unique. Qed.

Corollary label_of_bexp_unique : forall P b l,
  P |-b- b \in l ->
  l = label_of_bexp P b.
Proof. intro. apply label_of_exp_unique. Qed.

Corollary aexp_has_label_inj : forall P a l l',
  P |-a- a \in l ->
  P |-a- a \in l' ->
  l = l'.
Proof. intros. apply label_of_aexp_unique in H, H0. now rewrite_eq. Qed.

Corollary bexp_has_label_inj : forall P b l l',
  P |-b- b \in l ->
  P |-b- b \in l' ->
  l = l'.
Proof. intros. apply label_of_bexp_unique in H, H0. now rewrite_eq. Qed.

Fixpoint addr_sel_slh (P : pub_vars) (c : com) : com :=
  (match c with
  | <{{ skip }}> => <{{ skip }}>
  | <{{ x := e }}> => <{{ x := e }}>
  | <{{ c1; c2 }}> => <{{ addr_sel_slh P c1; addr_sel_slh P c2 }}>
  | <{{ if b then c1 else c2 end }}> => <{{ if b then "b" := (b ? "b" : 1); addr_sel_slh P c1 else
                                                  "b" := (b ? 1 : "b"); addr_sel_slh P c2 end }}>
  | <{{ while b do c end }}> => <{{ while b do "b" := (b ? "b" : 1); addr_sel_slh P c end; "b" := b ? 1 : "b" }}>
  | <{{ x <- a [[ i ]] }}> => let i' := if P x then <{ ("b" = 0) ? i : 0 }> else i in
                              <{{ x <- a [[ i' ]] }}>
  | <{{ a [ i ] <- e }}> => let i' := if label_of_aexp P e then i else <{ ("b" = 0) ? i : 0 }> in
                            <{{ a [ i' ] <- e }}>
  end)%string.

(** * Ideal small-step evaluation *)

Reserved Notation
  "P '|-' '<((' c , st , ast , b '))>' '-->i_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    pub_vars -> com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn  : forall P st ast b e n x,
      aeval st e = n ->
      P |- <((x := e, st, ast, b))> -->i_[]^^[] <((skip, x !-> n; st, ast, b))>
  | ISM_Seq : forall P c1 st ast b ds os c1t stt astt bt c2,
      P |- <((c1, st, ast, b))>  -->i_ds^^os <((c1t, stt, astt, bt))>  ->
      P |- <(((c1;c2), st, ast, b))>  -->i_ds^^os <(((c1t;c2), stt, astt, bt))>
  | ISM_Seq_Skip : forall P st ast b c2,
      P |- <(((skip;c2), st, ast, b))>  -->i_[]^^[] <((c2, st, ast, b))>
  | ISM_If : forall P be ct cf st ast b b' c',
      b' = beval st be ->
      c' = (if b' then ct else cf) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DStep]^^[OBranch b'] <((c', st, ast, b))>
  | ISM_If_F : forall P be ct cf st ast b b' c',
      b' = beval st be ->
      c' = (if b' then cf else ct) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DForce]^^[OBranch b'] <((c', st, ast, true))>
  | ISM_While : forall P be c st ast b,
      P |- <((while be do c end, st, ast, b))> -->i_[]^^[]
            <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall P x a ie st ast (b :bool) i,
      (if P x && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      P |- <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i]
            <((skip, x !-> (nth i (ast a) 0); st, ast, b))>
  | ISM_ARead_U : forall P x a ie st ast i a' i',
      aeval st ie = i ->
      P x = secret ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <((x <- a[[ie]], st, ast, true))> -->i_[DLoad a' i']^^[OARead a i]
            <((skip, x !-> (nth i' (ast a') 0); st, ast, true))>
  | ISM_Write : forall P a ie e st ast (b :bool) i n le,
      aeval st e = n ->
      P |-a- e \in le ->
      (if negb le && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      P |- <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i]
            <((skip, st, a !-> upd i (ast a) n; ast, b))>
  | ISM_Write_U : forall P a ie e st ast i n a' i',
      aeval st e = n ->
      P |-a- e \in public ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <((a[ie] <- e, st, ast, true))> -->i_[DStore a' i']^^[OAWrite a i]
            <((skip, st, a' !-> upd i' (ast a') n; ast, true))>

  where "P |- <(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step P c st ast b ct stt astt bt ds os).

Reserved Notation
  "P '|-' '<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (P:pub_vars) (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_ideal_refl : P |- <((c, st, ast, b))> -->i*_[]^^[] <((c, st, ast, b))>
  | multi_ideal_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      P |- <((c, st, ast, b))> -->i_ds1^^os1 <((c', st', ast', b'))> ->
      P |- <((c', st', ast', b'))> -->i*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      P |- <((c, st, ast, b))> -->i*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))>

  where "P |- <(( c , st , ast , b ))> -->i*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_ideal P c st ast b ct stt astt bt ds os).

Lemma multi_ideal_trans_nil_l P c st ast b c' st' ast' b' ct stt astt bt ds os :
  P |- <((c, st, ast, b))> -->i_[]^^[] <((c', st', ast', b'))> ->
  P |- <((c', st', ast', b'))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_trans_nil_r P c st ast b c' st' ast' b' ct stt astt bt ds os :
  P |- <((c, st, ast, b))> -->i_ds^^os <((c', st', ast', b'))> ->
  P |- <((c', st', ast', b'))> -->i*_[]^^[] <((ct, stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_combined_executions :
  forall P c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost,
    P |- <((c, st, ast, b))> -->i*_ds^^osm <((cm, stm, astm, bm))> ->
    P |- <((cm, stm, astm, bm))> -->i*_dsm^^ost <((ct, stt, astt, bt))> ->
    P |- <((c, st, ast, b))> -->i*_(ds++dsm)^^(osm++ost) <((ct, stt, astt, bt))>.
Proof.
  intros P c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost Hev1 Hev2.
  induction Hev1.
  - do 2 rewrite app_nil_l. apply Hev2.
  - do 2 rewrite <- app_assoc. eapply multi_ideal_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

Lemma multi_ideal_add_snd_com : forall P c st ast ct stt astt ds os c2 b bt,
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c;c2, st, ast, b))> -->i*_ds^^os <((ct;c2, stt, astt, bt))>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Conjecture addr_sel_slh_bcc : forall P c st ast (b:bool) ct stt astt bt ds os,
  nonempty_arrs ast ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <((addr_sel_slh P c, st, ast, b))> -->*_ds^^os <((ct, stt, astt, bt))> ->
  exists c', P |- <((c, st, ast, b))> -->i*_ds^^os <((c', "b" !-> st "b"; stt, astt, bt))>.

Conjecture gilles_lemma : forall P PA c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 ds os1 os2,
  P ;; PA |-ct- c ->
  pub_equiv P st1 st2 ->
  P |- <((c, st1, ast1, true))> -->i*_ds^^os1 <((ct1, stt1, astt1, true))> ->
  P |- <((c, st2, ast2, true))> -->i*_ds^^os2 <((ct2, stt2, astt2, true))> ->
  os1 = os2.

Conjecture ideal_eval_spec_ct_secure :
  forall P PA c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 ds os1 os2,
  P ;; PA |-ct- c ->
  unused "b" c ->
  st1 "b" = 0 ->
  st2 "b" = 0 ->
  pub_equiv P st1 st2 ->
  pub_equiv PA ast1 ast2 ->
  nonempty_arrs ast1 ->
  nonempty_arrs ast2 ->
  P |- <((c, st1, ast1, false))> -->i*_ds^^os1 <((ct1, stt1, astt1, bt1))> ->
  P |- <((c, st2, ast2, false))> -->i*_ds^^os2 <((ct2, stt2, astt2, bt2))> ->
  os1 = os2.

Conjecture addr_sel_slh_spec_ct_secure :
  forall P PA c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 ds os1 os2,
  P ;; PA |-ct- c ->
  unused "b" c ->
  st1 "b" = 0 ->
  st2 "b" = 0 ->
  pub_equiv P st1 st2 ->
  pub_equiv PA ast1 ast2 ->
  nonempty_arrs ast1 ->
  nonempty_arrs ast2 ->
  <((addr_sel_slh P c, st1, ast1, false))> -->*_ds^^os1 <((ct1, stt1, astt1, bt1))> ->
  <((addr_sel_slh P c, st2, ast2, false))> -->*_ds^^os2 <((ct2, stt2, astt2, bt2))> ->
  os1 = os2.
