(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp.
Require Import CRelationClasses Morphisms Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MFPROPERTIES.
Context (S T S' T': Type).

Lemma relcomp_inv (f: T ->> S') (g: S ->> T):
	(f o_R g) \inverse =~= (g \inverse) o_R (f \inverse).
Proof. by split; case => r []; exists r. Qed.

Notation "f '\is_section_of' g" := (f o g =~= F2MF id) (at level 2).

Lemma sec_cncl (f: S -> T) g:
	(F2MF f) \is_section_of (F2MF g) <-> cancel g f.
Proof.
split; last by intros; rewrite F2MF_comp /F2MF => s t; split => <-.
by move => eq s; move: (eq s s); rewrite (F2MF_comp _ g _ s) /F2MF /= => ->.
Qed.

Notation "f '\is_total'" := (dom f === All) (at level 2).

Lemma tot_spec Q Q' (f: Q ->> Q'): f \is_total <-> forall s, exists t, f s t.
Proof.
split => prp s //=.
by have /= -> := (prp s).
Qed.

Lemma comp_tot_dom R (f: S ->> T) (g: T ->> R):
	g \is_total -> (dom f) === (dom (g o f)).
Proof.
move => tot.
apply comp_dom_codom.
rewrite tot.
exact/subs_all.
Qed.

Lemma comp_tot R (f: S ->> T) (g: T ->> R):
	f \is_total -> g \is_total -> (g o f) \is_total.
Proof. by move => tot tot'; rewrite -comp_tot_dom. Qed.

Lemma F2MF_tot (f: S -> T):
	(F2MF f) \is_total.
Proof. by rewrite tot_spec; move => s; exists (f s). Qed.

(* For total multi valued functions, the relational composition is identical to the multi-
function composition.  *)
Lemma tot_comp R  (f : S ->> T) (g : R ->> S):
	f \is_total -> f o g =~= f o_R g.
Proof.
move => tot s t.
split => [ | comp]; first by case.
split => //.
rewrite tot; exact/ subs_all.
Qed.

(* the following should be called "is_mono" and "is_epi", but we consider the multi
valued functions to be functions and thus call the notions surjective and injective.
This will be further justified below when choice functions are introduced. *)
Definition mf_epi (f: S ->> T):= forall Q (g h: T ->> Q), g o f =~= h o f -> g =~= h.
Notation "f '\is_surjective'" := (mf_epi f) (at level 2).
Definition mf_mono (f: S ->> T):= forall Q (g h: Q ->> S), f o g =~= f o h -> g =~= h.
Notation "f '\is_mono'" := (mf_mono f) (at level 2).

(* For representations we should sieve out the single valued surjective partial functions. *)
Definition singlevalued S T (f: S ->> T) := (forall s t t', f s t -> f s t' -> t = t').
Notation "f '\is_singlevalued'" := (singlevalued f) (at level 2).

Global Instance sing_prpr S T: Proper ((@equiv S T) ==> iff) (@singlevalued S T).
Proof.
move => f f' feqf'; by split => sing s t t' fst fst'; apply /(sing s t t'); apply /feqf'.
Qed.

Lemma F2MF_sing (f: S-> T): (F2MF f) \is_singlevalued.
Proof. by move => s t t' H H0; rewrite -H0. Qed.

Lemma sing_rcomp R Q Q' (f: Q ->> Q') (g: R ->> Q):
	g \is_singlevalued -> f o g =~= f o_R g.
Proof.
move => sing s r.
split; first by case.
move => [t [gst ftr]].
split; first by exists t.
move => t' gst'.
by rewrite (sing s t' t) => //; exists r.
Qed.

Lemma sing_inj_comp_inv R Q Q' (f: Q ->> Q') (g: R ->> Q):
	g \is_singlevalued -> f\^-1 \is_singlevalued -> (f o g)\^-1 =~= (g\^-1) o (f\^-1).
Proof.
move => gsing finj.
rewrite (sing_rcomp f gsing).
rewrite (sing_rcomp (g\^-1) finj).
exact/rcomp_inv.
Qed.

Lemma sing_comp_inv (f: S ->> T):
	f \is_singlevalued -> f o (f\^-1) =~= mf_id|_(codom f).
Proof.
move => sing s t.
split => [[[r [fsr ftr]] dm] | ].
	split; first by exists r.
	by apply /sing; first apply /fsr.
move => [/dom_crct[t' fst'] <-].
split; first by exists t'.
by move => s'; exists s.
Qed.

Lemma mfinv_inj_sing (f: S -> T): injective f <-> (F2MF f)\^-1 \is_singlevalued.
Proof.
split => [inj s t t' eq eq' | sing s t eq]; first by apply inj; rewrite eq eq'.
by apply /sing; first by apply /eq.
Qed.

Lemma restr_sing_w (f: S ->> T) P:
	f \is_singlevalued -> (f \restricted_to P) \is_singlevalued.
Proof. by move => sing s t t' [_ fst [_ fst']]; apply (sing s t t'). Qed.

Lemma restr_sing (f: S ->> T) P Q:
	P \is_subset_of Q -> (f \restricted_to Q) \is_singlevalued -> (f \restricted_to P) \is_singlevalued.
Proof.
move => subs sing s t t' [Ps fst [_ fst']].
by apply /(sing s t t'); split => //; apply subs.
Qed.

Lemma empty_not_mono (s: S): ~(@empty_mf S T) \is_mono.
Proof.
move => inj.
pose g := F2MF (fun (b: bool) => s).
pose h := @empty_mf bool S.
suff eq: g =~= h by have /=<-:= eq true s.
apply inj.
by rewrite !comp_empty_l.
Qed.

Lemma empty_sing: (@empty_mf S T) \is_singlevalued.
Proof. done. Qed.

Lemma mono_tot (f: S ->> T): f \is_mono -> f \is_total.
Proof.
move => inj.
rewrite tot_spec => s.
apply not_all_not_ex => all.
pose g := F2MF (fun (b: bool) => s).
pose h := @empty_mf bool S.
suff eq: g =~= h by have /=<-:= eq true s.
apply inj.
rewrite F2MF_comp comp_empty_r => q r /=.
by split => // fsr; apply (all r).
Qed.

Lemma sing_tot_mono (f: S ->> T): (mf_inv f) \is_singlevalued -> f \is_total -> f \is_mono.
Proof.
move => sing /tot_spec tot R g h eq r s.
have [t fst]:= tot s.
have eq':= eq r t.
case: (classic (f o g r t)) => [cmp | ncmp].
	have: g r s.
		have [[s' [grs' fs't]] _]:= cmp.
		by rewrite (sing t s s').
	suff: h r s => //.
	move: cmp; rewrite eq'; move => [[s' [grs' fs't]] _].
	by rewrite (sing t s s').
have ngrs: ~ g r s.
	by move => grs; apply /ncmp /tot_comp; try rewrite tot_spec => //; exists s.
suff nhrs: ~ h r s => //.
move => hrs; apply /ncmp.
by rewrite eq'; apply /tot_comp; try rewrite tot_spec => //; exists s.
Qed.

Lemma comp_sing (f: T ->> T') (g : S ->> T) :
	f \is_singlevalued -> g \is_singlevalued -> (f o g) \is_singlevalued.
Proof.
move => fsing gsing r t t' [[] s [] grs fst _ [][] s' [] grs' fs't' _].
by rewrite (fsing s t t') => //; rewrite (gsing r s s').
Qed.

Lemma sing_comp R (f : S ->> T) (g : R ->> S):
	g \is_singlevalued -> g \is_total -> f o g =~= make_mf (fun r t => forall y, g r y -> f y t).
Proof.
move => sing /tot_spec tot.
split => [[[r [grs fst]] prop] y gsy | fgrt ]; first by rewrite (sing s y r).
split => [ | r gsr]; last by exists s0; apply/ (fgrt r).
by have [r gsr] := tot s; by exists r; split; last by apply fgrt.
Qed.

Lemma inv_dom_codom (f: S ->> T) t:
	t \from_codom f <-> t \from_dom (f \inverse).
Proof. exact/ codom_dom_inv. Qed.

Notation "f '\is_cototal'" := (codom f === All) (at level 2).

Lemma cotot_tot_inv (f: S ->> T):
	f \is_cototal <-> (f \inverse) \is_total.
Proof. by rewrite codom_dom_inv. Qed.

Lemma cotot_spec (f: S ->> T):
	f \is_cototal <-> forall t, exists s, f s t.
Proof.
by rewrite cotot_tot_inv tot_spec.
Qed.

(* Being surjective implies being cototal*)
Lemma sur_cotot f:
f \is_surjective -> f \is_cototal.
Proof.
move => fsur.
rewrite cotot_spec => t.
pose g := make_mf (fun t' b => t = t' /\ b = true).
pose h := make_mf (fun t' b => t = t' /\ b = false).
apply NNPP => notcodom.
have eq: g =~= h.
	apply (fsur bool g h) => s b.
	split => [] [[t' [val1 val2]] prop];
	by exfalso; apply notcodom; exists s; rewrite val2.1.
case: (classic (g t true)) => ass; last by apply ass.
by case: ((eq t true).1 ass).
Qed.

(* The opposite implication does not hold in general*)
Lemma cotot_notsur (f: S ->> T) (s: S) (t t': T):
	~ t = t' -> exists f, f \is_cototal /\ ~ f \is_surjective.
Proof.
move => neq.
pose f' := @make_mf S T (fun s t => True).
exists f'; split => [ | sur ].
	by rewrite cotot_spec; exists s.
pose g := make_mf (fun k b => k = t /\ b = true).
pose h := make_mf (fun k b => k = t /\ b = false).
suffices eq: g o f' =~= h o f'.
	have [a b]:= (((sur bool g h) eq) t false).
	by suffices htt: h t false by move: (b htt).2.
by split; move => [ [] _ [] _ [] _ _ prop];
	by have [ | b' [eq]]:= (prop t' _); last by exfalso; apply neq.
Qed.

(* but for single valued functions it is true. *)
Lemma sing_cotot_sur f:
f \is_singlevalued -> (f \is_cototal <-> f \is_surjective).
Proof.
split => [/cotot_spec fcotot Q g h eq t q| ]; last exact: sur_cotot.
split => ass; move: (fcotot t) => [] s fst.
	suffices gfsq: (g o f) s q.
		by move: ((eq s q).1 gfsq) => [] [] t' [] fst'; rewrite (H s t t').
	by split => [ | t' fst']; [exists t | exists q; rewrite (H s t' t)].
have hfsq: (h o f) s q.
	by split => [ | t' fst']; [ exists t| exists q; rewrite (H s t' t) ].
by move: ((eq s q).2 hfsq) => [] [] t' [] fst'; rewrite (H s t t').
Qed.

(* Due to the above, the following is named correctly.*)
Definition sur_par_fun S T (f: S ->> T) :=
  f \is_singlevalued /\ f \is_cototal.
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).

Definition sur_fun (f: S -> T) := forall t, exists s, f s = t.
Notation "f '\is_surjective_function'" := (sur_fun f) (at level 2).

Lemma sur_fun_sur (f: S -> T):
	f \is_surjective_function <-> (F2MF f) \is_surjective.
Proof.
split => sur.
	move => R g h.
	rewrite !F2MF_comp => eq s t.
	have [r <-]:= sur s.
	exact: (eq r t).
move => t.
have /cotot_spec cotot: (F2MF f) \is_cototal by apply sur_cotot.
have [s fst]:= cotot t.
by exists s.
Qed.
End MFPROPERTIES.
Notation "f '\is_mono'" := (mf_mono f) (at level 2).
Notation "f '\is_singlevalued'" := (singlevalued f) (at level 2).
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).
Notation "f '\is_surjective_function'" := (sur_fun f) (at level 2).
Notation "f '\is_total'" := (dom  f === All) (at level 2).
Notation "f '\is_cototal'" := (codom f === All) (at level 2).

Lemma comp_cotot R S T (f: R ->> T) (g: S ->> R):
	f \is_cototal -> g \is_cototal -> g \is_singlevalued -> (f o g) \is_cototal.
Proof.
rewrite !cotot_spec.
move => fct gct sing t.
have [r frt]:= fct t.
have [s gsr]:= gct r.
exists s.
split; first by exists r.
move => r' gsr'.
rewrite (sing s r' r) => //.
by exists t.
Qed.
