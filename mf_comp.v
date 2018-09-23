(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core.
Require Import CRelationClasses Morphisms.
 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section composition.
(* The difference between multivalued functions and relations is how they are composed:
The relational composition is given as follows.*)
Definition mf_rel_comp R S T (f : S ->> T) (g : R ->> S) :=
	make_mf (fun r t => (exists s, g r s /\ f s t)).
Notation "f 'o_R' g" := (mf_rel_comp f g) (at level 50).

Global Instance relcomp_prpr R S T:
Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@mf_rel_comp R S T).
Proof.
move => f f' eqf g g' eqg r t.
by split; move => [s [grs fst]]; exists s; by split; [apply /eqg | apply /eqf].
Qed.

Lemma relcomp_assoc S T S' T' (f: S' ->> T') g (h: S ->> T):
	((f o_R g) o_R h) =~= (f o_R (g o_R h)).
Proof.
split; last by move => [t' [[s' []]]]; exists s'; split => //; exists t'.
by move => [t' [hst [s'[]]]]; exists s'; split => //; exists t'.
Qed.

Lemma rcomp_inv R Q Q' (f: Q ->> Q') (g: R ->> Q):
	(f o_R g)\^-1 =~= (g\^-1) o_R (f\^-1).
Proof.
by move => r q'; split; move =>[q []]; exists q.
Qed.

(* The multi function composition adds an assumption that removes the symmetry of in- and output.
The additional condition is that g r is a subset of dom f. *)
Definition mf_comp R S T (f : S ->> T) (g : R ->> S) :=
	make_mf (fun r t => (f o_R g) r t /\ (g r) \is_subset_of (dom f)).
Notation "f 'o' g" := (mf_comp f g) (at level 50).

Global Instance comp_prpr R S T: Proper ((@equiv S T) ==> (@equiv R S) ==> (@equiv R T)) (@mf_comp R S T).
Proof.
move => f f' eqf g g' eqg s t; split; case.
	split; last by move => r g'sr; rewrite -eqf; apply/b/eqg.
	by move: a => [r stf]; exists r; rewrite -(eqf r t) -(eqg s r).
split; last by move => r g'sr; rewrite eqf; apply/b/eqg.
by move: a => [r stf]; exists r; rewrite (eqf r t) (eqg s r).
Qed.

Lemma comp_dom R Q Q' (f: Q ->> Q') (g: R ->> Q):
	dom (f o g) \is_subset_of dom g.
Proof. by move => r [s [[t[]]]]; exists t. Qed.

Lemma comp_subs_dom R S T (f: S ->> T) (g: T ->> R) s:
	f s \is_subset_of dom g -> s \from_dom f <-> s \from_dom (g o f).
Proof.
move => subs.
split; last by move => [r [[t [fst]]]]; exists t.
move => [t fst].
have [r gtr]:= subs t fst.
by exists r; split; first by exists t.
Qed.

Lemma comp_dom_codom R S T (f: S ->> T) (g: T ->> R):
	codom f \is_subset_of dom g -> dom f === dom (g o f).
Proof.
move => subs s; apply /comp_subs_dom => t fst.
by apply subs; exists s.
Qed.

Lemma comp_codom R S T (f: S ->> T) (g: T ->> R):
	codom (g o f) \is_subset_of codom g.
Proof. by move=> r /codom_crct [s] [[t [fst gtr]] _]; exists t. Qed.

Lemma comp_codom_dom R S T (f: S ->> T) (g: T ->> R):
	codom f \is_subset_of dom g -> codom g|_(codom f) === codom (g o f).
Proof.
move => subs r.
split.
	move => /codom_crct [t [/codom_crct [s fst] gtr]].
	rewrite codom_crct; exists s.
	split => [ | t' fst']; first by exists t.
	by apply subs; exists s.
move => /codom_crct [s [[t [fst gtr]]] subs'].
by rewrite codom_crct; exists t; split; first exists s.
Qed.

(* This operation is associative *)
Lemma comp_assoc S T S' T' (f: S' ->> T') g (h: S ->> T):
	((f o g) o h) =~= (f o (g o h)).
Proof.
move => r q.
split => [ [] [] s [] hrs [] [] t []| [] [] t [] [] [] s [] ].
	split => [ | t' [] [] s' [] hrs'].
		exists t;	split => //; split => [ | s' hrs']; first by exists s.
		by move: (b1 s' hrs') => [] x [] [] t' []; exists t'.
	by move: (b1 s' hrs') => [] q' comp gs't _; apply comp.2.
split => [ | s' hrs'].
	exists s; split => //.
	split => [ | t' gst']; first by exists t.
	suffices ghrs: (g o h) r t' by apply (b2 t' ghrs).
	by split => [ | s' hrs']; [exists s | apply b0].
move: (b0 s' hrs') => [] t' gs't'.
have ghrt': (g o h) r t'
	by split => [ | s'' hrs'']; [exists s' | apply b0].
move: (b2 t' ghrt') => [] q' ft'q'; exists q'.
split => [ | t'' gs't'']; first by exists t'.
suffices ghrt'': (g o h) r t'' by apply b2.
by split => [ | s'' hrs'']; [exists s' | apply b0].
Qed.

Lemma comp_id_restr S T (f: S ->> T) P: f o mf_id|_P =~= f|_P.
Proof.
move => s t.
split; first by move => [[_ [[Ps <-]]]].
move => [ps fst].
split; first by exists s.
by move => t' [_ <-]; exists t.
Qed.

Lemma comp_id_l S T (f: S ->> T):
	mf_id o f =~= f.
Proof.
split => [[[t' [fst <-]] _] | fst] //; by split => [ | t' fst']; [exists s0 | exists t'].
Qed.

Lemma comp_id_r S T (f: S ->> T):
	f o mf_id =~= f.
Proof.
split => [[[t' [<- fst]] _] | fst] //; by split => [| t' <- ]; [exists s|exists s0].
Qed.

Lemma comp_empty_l S T R (f: S ->> T): (@empty_mf T R) o f =~= (@empty_mf S R).
Proof. by split => //=; move => [[a []]]. Qed.

Lemma comp_empty_r S T R (f: S ->> T): f o (@empty_mf R S) =~= (@empty_mf R T).
Proof. by split => //=; move => [[a []]]. Qed.

Lemma comp_F2MF R S T (f: S ->> T) (g: R -> S):
	(f o (F2MF g)) =~= mf.Pack (fun r => f (g r)).
Proof.
split => [[[r [/=-> fst]] prop] | fgrt] //.
by split => [ | r eq]; [exists (g s) | exists s0; rewrite -eq].
Qed.

Lemma F2MF_comp R S T (f: S ->> T) (g: R -> S):
	(f o (F2MF g)) =~= mf.Pack (fun r => f (g r)).
Proof. exact/comp_F2MF. Qed.

Lemma F2MF_comp_F2MF R S T (f: S -> T) (g: R -> S):
	(F2MF f o F2MF g) =~= F2MF (fun r => f (g r)).
Proof. by move => s t; rewrite F2MF_comp /=. Qed.

Definition cnst S T (c: T) := (fun (_: S) => c).
Arguments cnst {S} {T}.

Definition mf_cnst S T (c: T) := F2MF (@cnst S T c).
Arguments mf_cnst {S} {T}.

Lemma cnst_comp R S T (c: T) (f: R ->> S): (mf_cnst c) o f =~= (mf_cnst c)|_(dom f).
Proof.
move => r t.
split; first by rewrite /=/cnst; move => [[s [frs /=->]] _]; split => //; exists s.
move => [[s fsr <-]]; split; first by exists s.
by move => a b; exists c.
Qed.
End composition.
Arguments cnst {S} {T}.
Arguments mf_cnst {S} {T}.
Notation "f 'o_R' g" := (mf_rel_comp f g) (at level 2).
Notation "f 'o' g" := (mf_comp f g) (at level 2).