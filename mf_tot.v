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