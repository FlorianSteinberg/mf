(******************************************************************************)
(* Some lemmas about multivalued functions that are only true if classical    *)
(* reasoning is used. This file is not exported by all_mpf and has to be      *)
(* imported separately.                                                       *)
(******************************************************************************)
From mathcomp Require Import ssreflect ssrfun.
Require Import all_mf.
Require Import Classical ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope mf_scope.
Section classical_mf.
Context (S T: Type).

Lemma mono_tot (f: S ->> T): f \is_mono -> f \is_total.
Proof.
move => inj s.
apply not_all_not_ex => all.
pose g := F2MF (fun (b: bool) => s).
pose h := @mf_empty bool S.
suff eq: g =~= h by have /=<-:= eq true s.
apply inj.
rewrite comp_F2MF comp_empty_r => q r /=.
by split => // fsr; apply (all r).
Qed.

Lemma sing_tot_mono (f: S ->> T): (f\^-1) \is_singlevalued -> f \is_total -> f \is_mono.
Proof.
move => sing tot R g h eq r s.
have [t fst]:= tot s.
have eq':= eq r t.
case: (classic (t \from (f \o g) r)) => [cmp | ncmp].
- have: s \from g r.
  + have [[s' [grs' fs't]] _]:= cmp.
    by rewrite (sing t s s').
  suff: s \from h r => //.
  move: cmp; rewrite eq'; move => [[s' [grs' fs't]] _].
  by rewrite (sing t s s').
have ngrs: ~ g r s by move => grs; apply/ncmp/comp_rcmp => //; exists s.
suff nhrs: ~ h r s => //.
by move => hrs; apply /ncmp; rewrite eq'; apply /comp_rcmp => //; exists s.
Qed.

Lemma epi_cotot (f: S ->> T): f \is_epi -> f \is_cototal.
Proof.
move => fsur t.
pose g := make_mf (fun t' b => t = t' /\ b = true).
pose h := make_mf (fun t' b => t = t' /\ b = false).
apply NNPP => notcodom.
have eq: g =~= h.
- apply (fsur bool g h) => s b.
  by split => [] [[t' [val1 val2]] prop];
   exfalso; apply notcodom; exists s; rewrite val2.1.
case: (classic (g t true)) => ass; last by apply ass.
by case: ((eq t true).1 ass).
Qed.

Lemma cotot_epi (f: S ->> T):
f \is_singlevalued -> (f \is_cototal <-> f \is_epi).
Proof.
split => [fcotot Q g h eq t q| ]; last exact: epi_cotot.
split => ass; move: (fcotot t) => [] s fst.
	suffices gfsq: (g \o f) s q.
		by move: ((eq s q).1 gfsq) => [] [] t' [] fst'; rewrite (H s t t').
	by split => [ | t' fst']; [exists t | exists q; rewrite (H s t' t)].
have hfsq: (h \o f) s q.
	by split => [ | t' fst']; [ exists t| exists q; rewrite (H s t' t) ].
by move: ((eq s q).2 hfsq) => [] [] t' [] fst'; rewrite (H s t t').
Qed.

Lemma sur_fun_sur (f: S -> T):
	f \is_surjective <-> (F2MF f) \is_epi.
Proof. rewrite F2MF_cotot -cotot_epi//; exact/F2MF_sing. Qed.
End classical_mf.


Section choice_mf.
  Context (S T: Type).

  Lemma choice_spec:
    FunctionalChoice_on S T <-> (forall (F: S ->> T), F \is_total -> exists f, f \is_choice_for F).
  Proof.
    split => [choice F /choice [f fprp] | icf R tot].
    - by exists f => s sfd; apply/fprp.
    have [ | f fprp]:= icf (make_mf R); first exact/tot.
    exists f => s; apply/fprp.
    have [t val]:= tot s.
    exists t; apply/val.
  Qed.                                                   
    
  Lemma exists_pchoice (F: S ->> T):
    FunctionalChoice_on S (option T) -> exists f, (pf2MF f) \tightens F.
  Proof.
    move => choice.
    pose R s ot := s \from dom F -> exists t, ot = some t /\ t \from F s.
    have [s | f fprp]:= choice R.
    - case: (classic (s \from dom F)) => [[t Fst] | fls]; first by exists (some t); exists t.
      by exists None => sfd; exfalso; apply/fls.
    exists f => s sfd; have [t [eq val]]:= fprp s sfd.
    by split => [ | t' /=]; [exists t; rewrite /= eq | rewrite eq => <-].
  Qed.

  Lemma exists_choice (F: S ->> T) (t: T):
    FunctionalChoice_on S T -> exists f, f \is_choice_for F.
  Proof.
    move => choice.
    pose R s t := forall Fs, F s Fs -> F s t.
    have [s | f tot]:= choice R; last by exists f => s [fs fsfs]; apply/tot/fsfs.
    case: (classic (s \from dom F)) => [[] t' fst | false]; first by exists t'.
    by exists t => t' fst'; exfalso; apply false; exists t'.
  Qed.

  Lemma fun_spec (f: S ->> T) (t: T):
    FunctionalChoice_on S T -> f \is_function <-> f \is_singlevalued /\ f \is_total.
  Proof.
    move => choice.
    split => [ [g eq] | [sing tot]].
    - by split; rewrite -eq; [apply F2MF_sing | apply F2MF_tot].
    have [ | g icf]//:= exists_choice f t.
    by exists g; apply/sing_tot_F2MF_icf.
  Qed.

  Lemma icf_tight (g f: S ->> T):
    FunctionalChoice_on S T ->
    (forall s, exists t', ~ f s t')
    -> (forall h, (h \is_choice_for g -> h \is_choice_for f)) -> (g \tightens f).
  Proof.
    move => choice ex prop s sfd.
    split => [ | t' gst'].
    - have [t' nfst']:= (ex s).
      pose g' := make_mf (fun x y => (x <> s -> g x y) /\ (x = s -> y = t')).
      have [ | h icf']// := (exists_choice g' t').
      apply NNPP => nex.
      have ngst': ~g s t' by move => gst'; apply nex; exists t'.
      have icf: h \is_choice_for g.
      + move => s' [t'' gs't''].
	case (classic (s' = s)) => [eq | neq].        
	* by exfalso; apply nex; exists t''; rewrite -eq.
	have g's't'': g' s' t'' by split => // eq; exfalso; apply neq.
        by apply/((icf' s' _).1 neq); exists t''.
      suffices eq: h s = t' by apply nfst'; rewrite -eq; apply: (prop h icf s).
      have g'st': g' s t' by trivial.
      by apply/(icf' s _).2; first exists t'.
    pose g' := make_mf (fun x y => g x y /\ (x = s -> y = t')).
    have gtg: g' \tightens g.
    - move => x xfd.
      split => [ | y g'xy]; last by apply g'xy.1.
      case (classic (x = s)) => [ eq | neq ]; first by exists t'; rewrite eq.
      by have [y gxy]:= xfd; exists y; by split.
    have [ | h icf'] //:= (exists_choice g' t').
    have icf: h \is_choice_for g.
    - apply icf_spec.
      apply/ tight_trans; first by apply/ gtg.
      by apply icf_spec; apply icf'.
    suffices val: h s = t' by rewrite -val; apply/ (prop h icf s _).
    have val': g s t' /\ (s = s -> t' = t') by split.
    by apply: (icf' s _).2; first exists t'.
  Qed.
End choice_mf.

Lemma pfun_spec S T (f: S ->> T): FunctionalChoice_on S (option T) ->
  f \is_partial_function <-> f \is_singlevalued.
Proof.
  move => choice.
  split => [[g <-] | sing]; first exact/pf2MF_sing.
  pose F:= make_mf (fun s t =>
    (exists t', t = Some t' /\ f s t') \/ (~ s \from dom f /\ t = None)).
  have [ | g icf]//:= exists_choice F None.
  have: F \is_total => [s' | tot].
  - case: (classic (s' \from dom f)) => [[fs' fs'fs'] | neg]; last by exists None; right.
    by exists (Some (fs')); left; exists fs'.
  exists g => s t /=.
  case E: (g s) => [gs |].
  - have [[t' []] | []]:= icf s (tot s); last by rewrite E.
    by rewrite E => [[<- fsgs]]; split => [<- | fst]//; apply/sing/fst.
  by split => // fst; have [[t' []] | [ndm _]]:= icf s (tot s); [rewrite E |apply ndm; exists t].
Qed.