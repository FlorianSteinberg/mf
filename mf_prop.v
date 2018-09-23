From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section totals.
Context (S T S' T': Type).
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

Notation "f '\is_cototal'" := (codom f === All) (at level 2).

Lemma cotot_tot_inv (f: S ->> T):
	f \is_cototal <-> (f \inverse) \is_total.
Proof. by rewrite codom_dom_inv. Qed.

Lemma cotot_spec (f: S ->> T):
	f \is_cototal <-> forall t, exists s, f s t.
Proof.
by rewrite cotot_tot_inv tot_spec.
Qed.
End totals.
Notation "f '\is_total'" := (dom  f === All) (at level 2).
Notation "f '\is_cototal'" := (codom f === All) (at level 2).

Section singlevalueds.
Context (S T S' T': Type).
(* For representations we should sieve out the single valued surjective partial functions. *)
Definition singlevalued S T (f: S ->> T) := (forall s t t', f s t -> f s t' -> t = t').
Notation "f '\is_singlevalued'" := (singlevalued f) (at level 2).

Global Instance sing_prpr S T: Proper ((@equiv S T) ==> iff) (@singlevalued S T).
Proof.
move => f f' feqf'; by split => sing s t t' fst fst'; apply /(sing s t t'); apply /feqf'.
Qed.

Lemma empty_sing: (@empty_mf S T) \is_singlevalued.
Proof. done. Qed.

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

Lemma comp_cotot R (f: R ->> T) (g: S ->> R):
	g \is_singlevalued -> f \is_cototal -> g \is_cototal -> (f o g) \is_cototal.
Proof.
rewrite !cotot_spec.
move => sing fct gct t.
have [r frt]:= fct t.
have [s gsr]:= gct r.
exists s.
split; first by exists r.
move => r' gsr'.
rewrite (sing s r' r) => //.
by exists t.
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
End singlevalueds.
Notation "f '\is_singlevalued'" := (singlevalued f) (at level 2).

Section epi_mono.
Context (S T S' T': Type).
(* the following are taken from category theory. *)
Definition mf_epi (f: S ->> T):= forall Q (g h: T ->> Q), g o f =~= h o f -> g =~= h.
Notation "f '\is_epi'" := (mf_epi f) (at level 2).
Definition mf_mono (f: S ->> T):= forall Q (g h: Q ->> S), f o g =~= f o h -> g =~= h.
Notation "f '\is_mono'" := (mf_mono f) (at level 2).

Lemma empty_not_mono (s: S): ~(@empty_mf S T) \is_mono.
Proof.
move => inj.
pose g := F2MF (fun (b: bool) => s).
pose h := @empty_mf bool S.
suff eq: g =~= h by have /=<-:= eq true s.
apply inj.
by rewrite !comp_empty_l.
Qed.

(* Classically, being surjective implies being cototal (see file classical_mf.v).
The opposite implication does not hold in general *)
Lemma cotot_notepi (f: S ->> T) (s: S) (t t': T):
	~ t = t' -> exists f, f \is_cototal /\ ~ f \is_epi.
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

(* Again Classically, the inverse is true for singlevalud functions (see classical_mf.v).
Thus the following is named correctly. *)
Definition sur_par_fun S T (f: S ->> T) :=
  f \is_singlevalued /\ f \is_cototal.

Definition sur_fun (f: S -> T) := forall t, exists s, f s = t.
End epi_mono.
Notation "f '\is_mono'" := (mf_mono f) (at level 2).
Notation "f '\is_epi'" := (mf_epi f) (at level 2).
Notation "f '\is_surjective_partial_function'" := (sur_par_fun f) (at level 2).
Notation "f '\is_surjective_function'" := (sur_fun f) (at level 2).