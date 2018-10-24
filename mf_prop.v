From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_comp mf_rcmp.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section totals.
Definition total S T := make_subset (fun (f: S ->> T) => (forall s, s \from dom f)).
Notation "f \is_total" := (f \from (total _ _ )) (at level 30).

Global Instance tot_prpr S T: Proper ((@equiv S T) ==> iff) (@total S T).
Proof.
by move => f g eq; split => tot s; have [t]:= tot s; exists t; [rewrite -eq| rewrite eq].
Qed.

Context (S T S' T': Type).

Lemma tot_spec Q Q' (f: Q ->> Q'): f \is_total <-> (dom f === All).
Proof. by split => prp s; [have /=:= prp s | rewrite prp]. Qed.

Lemma rcmp_tot_dom R (f: S ->> T) (g: T ->> R):
	g \is_total -> (dom f) === (dom (g o_R f)).
Proof.
move => tot s; split => [[t frt] | [r [t []]]]; last by exists t.
by have[r gtr]:= tot t; exists r; exists t.
Qed.

Lemma comp_tot_dom R (f: S ->> T) (g: T ->> R):
	g \is_total -> (dom f) === (dom (g o f)).
Proof.
move => /tot_spec tot.
apply comp_dom_codom.
rewrite tot; exact/subs_all.
Qed.

Lemma comp_tot R (f: S ->> T) (g: T ->> R):
	f \is_total -> g \is_total -> (g o f) \is_total.
Proof. by move => /tot_spec tot tot'; apply/tot_spec; rewrite -comp_tot_dom. Qed.

Lemma rcmp_tot R (f: S ->> T) (g: T ->> R):
	f \is_total -> g \is_total -> (g o_R f) \is_total.
Proof. by move => /tot_spec tot tot'; apply/tot_spec; rewrite -rcmp_tot_dom. Qed.

Lemma tot_subs_dom R (f: S ->> T) (g: S ->> T) (h: T ->> R):
	codom g \is_subset_of dom h-> dom (h o g) \is_subset_of dom (h o f) -> dom g \is_subset_of dom f.
Proof.
move => tot dm s [t gst].
have [ | r [[t' []]]]:= dm s; last by exists t'.
have [ | r htr] //:= tot t; first by exists s.
by exists r; split => [ | t' gst']; [exists t | apply tot; exists s].
Qed.

Lemma F2MF_tot (f: S -> T):
	(F2MF f) \is_total.
Proof. by move => s; exists (f s). Qed.

(* For total multi valued functions, the relational composition is identical to the multi-
function composition.  *)
Lemma comp_rcmp R  (f : S ->> T) (g : R ->> S):
	f \is_total -> f o g =~= f o_R g.
Proof.
move => /tot_spec tot s t; split => [ | comp]; first by case.
by split => //; rewrite tot; exact/ subs_all.
Qed.

Definition cototal S T:= make_subset (fun (f: S ->> T) =>
	forall t, t \from codom f).
Notation "f '\is_cototal'" := (f \from (cototal _ _)) (at level 30).

Lemma cotot_spec (f: S ->> T): f \is_cototal <-> codom f === All.
Proof. by split => ass s; first split => // _; apply/ass. Qed.

Lemma cotot_tot_inv (f: S ->> T):
	f \is_cototal <-> (f \inverse) \is_total.
Proof. by rewrite cotot_spec codom_dom_inv tot_spec. Qed.
End totals.
Notation "f '\is_total'" := (f \from (total _ _)) (at level 2).
Notation "f '\is_cototal'" := (f \from (cototal _ _)) (at level 2).

Section singlevalueds.
Context (S T S' T': Type).
(* For representations we should sieve out the single valued surjective partial functions. *)
Definition singlevalued S T := make_subset (fun (f: S ->> T) =>
	forall s t t', f s t -> f s t' -> t = t').
Notation "f '\is_singlevalued'" := (f \from (singlevalued _ _)) (at level 2).

Global Instance sing_prpr S T: Proper ((@equiv S T) ==> iff) (@singlevalued S T).
Proof. by split => sing s t t' fst fst'; apply /(sing s t t'); apply /H. Qed.

Lemma empty_sing: (@empty_mf S T) \is_singlevalued.
Proof. done. Qed.

Lemma F2MF_sing (f: S-> T): (F2MF f) \is_singlevalued.
Proof. by move => s t t' H H0; rewrite -H0. Qed.

Lemma sing_rcmp R Q Q' (f: Q ->> Q') (g: R ->> Q):
	g \is_singlevalued -> f o g =~= f o_R g.
Proof.
move => sing s r.
split => [ | [t [gst ftr]]]; first by case.
split => [ | t' gst']; first by exists t.
by rewrite (sing s t' t) => //; exists r.
Qed.

Lemma rcmp_cotot R (f: R ->> T) (g: S ->> R):
	f \is_cototal -> g \is_cototal -> (f o_R g) \is_cototal.
Proof. by move => fct gct t; have [r frt]:= fct t; have [s gsr]:= gct r; exists s; exists r. Qed.

Lemma comp_cotot R (f: R ->> T) (g: S ->> R):
	g \is_singlevalued -> f \is_cototal -> g \is_cototal -> (f o g) \is_cototal.
Proof.
move => sing fct gct t.
have [r frt]:= fct t; have [s gsr]:= gct r.
exists s; split => [ | r' gsr']; first by exists r.
by rewrite (sing s r' r) => //; exists t.
Qed.

Lemma sing_inj_comp_inv R Q Q' (f: Q ->> Q') (g: R ->> Q):
	g \is_singlevalued -> f\^-1 \is_singlevalued -> (f o g)\^-1 =~= (g\^-1) o (f\^-1).
Proof. by move => gsing finj; rewrite !sing_rcmp //; apply/rcmp_inv. Qed.

Lemma sing_comp_inv (f: S ->> T):
	f \is_singlevalued -> f o (f\^-1) =~= mf_id|_(codom f).
Proof.
move => sing.
split => [[[r [frs frt]] dm] | [[t' fst'] <-]]; first by split; [exists r | apply /sing/frt].
by split => [ | s']; [exists t' | exists s].
Qed.

Lemma mfinv_inj_sing (f: S -> T): injective f <-> (F2MF f)\^-1 \is_singlevalued.
Proof. by split => [inj s t t' eq eq' | sing s t eq]; [apply/inj; rewrite eq eq' | apply/sing]. Qed.

Lemma restr_sing_w (f: S ->> T) P: f \is_singlevalued -> (f \restricted_to P) \is_singlevalued.
Proof. by move => sing s t t' [_ fst [_ fst']]; apply (sing s t t'). Qed.

Lemma restr_sing (f: S ->> T) P Q:
	P \is_subset_of Q -> (f \restricted_to Q) \is_singlevalued -> (f \restricted_to P) \is_singlevalued.
Proof.
by move => subs sing s t t' [Ps fst [_ fst']]; apply/sing; split; try apply/subs; try apply/fst.
Qed.

Lemma comp_sing (f: T ->> T') (g : S ->> T) :
	f \is_singlevalued -> g \is_singlevalued -> (f o g) \is_singlevalued.
Proof.
move => fsing gsing r t t' [[] s [] grs fst _ [][] s' [] grs' fs't' _].
by rewrite (fsing s t t') => //; rewrite (gsing r s s').
Qed.

Lemma rcmp_sing (f: T ->> T') (g : S ->> T) :
	f \is_singlevalued -> g \is_singlevalued -> (f o_R g) \is_singlevalued.
Proof.
move => fsing gsing r t t' [s [grs fst]] [s' [grs' fs't]].
by rewrite (fsing s t t') => //; rewrite (gsing r s s').
Qed.

Lemma sing_comp R (f : S ->> T) (g : R ->> S):
	g \is_singlevalued -> g \is_total -> f o g =~= make_mf (fun r t => forall y, g r y -> f y t).
Proof.
move => sing tot.
split => [[[r [grs fst]] prop] y gsy | fgrt ]; first by rewrite (sing s y r).
split => [ | r gsr]; last by exists s0; apply/ (fgrt r).
by have [r gsr] := tot s; by exists r; split; last by apply fgrt.
Qed.
End singlevalueds.
Notation "f '\is_singlevalued'" := (f \from (singlevalued _ _)) (at level 2).

Section epi_mono.
Context (S T S' T': Type).
(* the following are taken from category theory. *)
Definition epimorphism := make_subset (fun (f: S ->> T) =>
	forall Q (g h: T ->> Q), g o f =~= h o f -> g =~= h).
Notation "f '\is_epi'" := (epimorphism f) (at level 2).
Definition monomorphism := make_subset (fun (f: S ->> T) =>
	forall Q (g h: Q ->> S), f o g =~= f o h -> g =~= h).
Notation "f '\is_mono'" := (monomorphism f) (at level 2).

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
exists f'; split => [ | sur ]; first by exists s.
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
Definition surjective_partial_function := intersection (singlevalued S T) (cototal S T).

Definition functions := make_subset (fun F => exists (f: S -> T), F2MF f = F).

Lemma func_spec: functions === codom (F2MF (@F2MF S T)).
Proof. done. Qed.

Definition surjective_function := make_subset (fun (f: S -> T) => forall t, exists s, f s = t).
End epi_mono.
Notation "f '\is_mono'" := (f \from (monomorphism _ _)) (at level 2).
Notation "f '\is_epi'" := (f \from (epimorphism _ _)) (at level 2).
Notation "f '\is_surjective_partial_function'" := (f \from (surjective_partial_function _ _)) (at level 2).
Notation "f '\is_surjective_function'" := (f \from (surjective_function _ _)) (at level 2).