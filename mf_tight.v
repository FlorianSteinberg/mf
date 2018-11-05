(* This file contains basic definitions and Lemmas about multi-valued functions *)
From mathcomp Require Import all_ssreflect.
Require Import mf_set mf_core mf_rcmp mf_comp mf_tot mf_sing.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition exte S T (f g: S ->> T) := forall s, f s \is_subset_of g s.
Notation "g '\extends' f" := (exte f g) (at level 50).
Definition mf_exte S T := make_mf (@exte S T).
Arguments mf_exte {S} {T}.

Global Instance exte_prpr S T: Proper (@equiv S T ==> @equiv S T ==> iff) (@exte S T).
Proof. by move => f f' feq g g' geq; split => exte s t gst; apply/geq/exte/feq. Qed.

Definition tight S T (g f: S ->> T):=
	forall s, s \from dom g -> s \from dom f /\ forall t, f s t -> g s t.
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).
Definition mf_tight S T:= make_mf (@tight S T).
Arguments mf_tight {S} {T}.

Global Instance tight_prpr S T:
	Proper ((@equiv S T) ==> (@equiv S T) ==> iff) (@tight S T).
Proof.
move => f f' eqf g g' eqg.
split => tight s sfd; split => [ | t gst].
			by rewrite -eqg; have [ | fd prp]:= tight s; first by rewrite eqf.
		by have [ | fd prp]:= tight s; [rewrite eqf| rewrite -(eqf s t); apply prp; rewrite (eqg s t)].
	by rewrite eqg; have [ | fd prp]:= tight s; first by rewrite -eqf.
by have [ | fd prp]:= tight s; [rewrite -eqf| rewrite (eqf s t); apply prp; rewrite -(eqg s t)].
Qed.

Section tight.
Context (S T: Type).

Lemma split_tight (f g: S ->> T):
	(dom g) \is_subset_of (dom f) -> (forall s, s \from dom g -> (f s) \is_subset_of (g s)) ->
		f \tightens g.
Proof. by move => dm val; split; [apply/dm | apply/val]. Qed.

Lemma tight_dom (f g: S ->> T):
	f \tightens g -> (dom g) \is_subset_of (dom f).
Proof. by move => tight s sfd; have []:= tight s sfd. Qed.

Lemma tight_val (f g: S ->> T) s:
	f \tightens g -> s \from dom g -> (f s) \is_subset_of (g s).
Proof. by move => tight sfd; have []:= tight s sfd. Qed.

Lemma tight_spec (f g: S ->> T):
	f \tightens g <-> dom g \is_subset_of dom f /\ g \extends f|_(dom g).
Proof.
split => [tight | [subs exte]]; last by apply/split_tight => // s sfd t' fst'; apply/exte.
by split => [ | s t [sfd]]; [apply/tight_dom | apply/tight_val].
Qed.

Lemma tight_equiv (f g: S ->> T): f \tightens g -> g \tightens f -> f =~= g.
Proof.
move => tight tight' s t; split => [fst | gst].
	by apply /(tight_val tight); first by apply /(tight_dom tight'); exists t.
by apply /(tight_val tight'); first by apply /(tight_dom tight); exists t.
Qed.

Lemma exte_equiv (f g: S ->> T) : f =~= g <-> f \extends g /\ g \extends f.
Proof.
split => [eq | [gef feg] s t]; first by split => s t val; apply/eq.
by split => ass; [apply/feg | apply/gef].
Qed.

Lemma exte_restr (f: S ->> T) P Q: P \is_subset_of Q -> f|_Q \extends f|_P.
Proof. by move => subs s t []; split => //; apply subs. Qed.

(* tight is almost an equivalence relation, it only fails to be symmetric *)
Global Instance tight_ref: Reflexive (@tight S T).
Proof. done. Qed.

Global Instance tight_trans:
	Transitive (@tight S T).
Proof.
move => f g h tight tight'.
apply /split_tight => [ | s sfd]; first exact/subs_trans/tight_dom/tight'/tight_dom.
exact/subs_trans/tight_val/sfd/tight/tight_val/tight_dom/sfd.
Qed.

Lemma sing_tight_exte (f: S ->> T) g:
	f \is_singlevalued -> g \tightens f -> g \extends f.
Proof.
move => sing tight s t fst.
have sfd: s \from dom f by exists t.
have [t' gst']:= tight_dom tight sfd.
rewrite (sing s t t') //.
exact/tight_val/gst'.
Qed.

Lemma mf_tight_exte:
	mf_exte|_(singlevalued S T) \extends mf_tight|_(singlevalued S T).
Proof. by move => f [g] []; split; last apply/sing_tight_exte. Qed.

Lemma exte_dom (f g: S ->> T):
	g \extends f -> (dom f) \is_subset_of (dom g).
Proof. by move => exte s [t fst]; exists t; apply exte. Qed.

Lemma sing_exte_tight (f: S ->> T) g:
	g \is_singlevalued -> g \extends f -> g \tightens f.
Proof.
move => gsing exte.
apply split_tight => s [t]; first by exists t; apply exte.
move => fst t' gst'; have gst := exte s t fst.
by rewrite (gsing s t' t).
Qed.

Lemma mf_exte_tight:
	mf_tight|^(singlevalued S T) \extends mf_exte|^(singlevalued S T).
Proof. by move => f [g] []; split; last apply/sing_exte_tight. Qed.

Lemma exte_tight (f: S ->> T) g:
	f \is_singlevalued -> g \is_singlevalued -> (g \extends f <-> g \tightens f).
Proof. split; [exact: sing_exte_tight | exact: sing_tight_exte] . Qed.

Lemma exte_sing (f: S ->> T) (g: S ->> T):
	f \extends g -> f \is_singlevalued -> g \is_singlevalued.
Proof. move => exte sing s t t' gst gst'; apply /sing; apply exte; [apply gst | apply gst']. Qed.

Lemma exte_comp R (f f': T ->> R) (g: S ->> T):
	f \extends f' -> (f o g) \extends (f' o g).
Proof.
move => fef s r [[t [gst ftr] prop]].
split => [ | t' gst']; first by exists t; split => //; apply fef.
specialize (prop t' gst').
have [r' f't'r']:= prop.
by exists r'; apply fef.
Qed.

Lemma tight_restr_w (f: S ->> T) P: f \tightens (f|_P).
Proof. by move => s [t [Ps fst]]; by split; first by exists t. Qed.

Lemma tight_restr_r (f g: S ->> T) P Q:
	P \is_subset_of Q -> f \tightens (g|_Q) -> f \tightens (g|_P).
Proof.
move => subs tight s dm.
split => [ | t fst /=]; first by apply/tight_dom; first exact/tight; first exact/dom_restr_subs/dm.
split; first by move: dm => [t' /= []].
suff: g|_Q s t by rewrite /= => [[]].
by apply /tight_val /fst/dom_restr_subs/dm.
Qed.

Lemma tight_restr_l (f g: S ->> T) P Q:
	P \is_subset_of Q -> (f|_P) \tightens g -> (f|_Q) \tightens g.
Proof.
move => subs tight s [t gst].
have [ | [t' [Ps fst'] prp]]:= tight s; first by exists t.
split => [ | t'' [Qs fst'']]; first by exists t'; split; try apply subs.
by apply prp.
Qed.

Lemma tight_restr (f: S ->> T) P Q:
	P \is_subset_of Q -> (f|_Q) \tightens (f|_P).
Proof. by move => subs; apply /(tight_restr_l subs)/tight_ref. Qed.

Lemma tight_comp_r R (f: T ->> R) g (g': S ->> T):
	g \tightens g' -> (f o g) \tightens (f o g').
Proof.
move => gtg' s [r [[t [g'st ftr]] prop]].
have sfd: s \from dom g' by exists t.
have [t' gst']:= (gtg' s sfd).1.
have g'st': g' s t' by apply (gtg' s sfd).2.
move: (prop t' g'st') => [r' fgsr'].
split; first exists r'.
	split => [ | t'' gst'']; first by exists t'.
	by apply prop; apply (gtg' s sfd).2.
move => r'' [[t'' [gst'' ft''r'']] prop'].
split => //; by exists t''; split => //; apply (gtg' s sfd).2.
Qed.

Lemma tight_exte_dom (f g: S ->> T):
	g \extends f -> f \tightens (g \restricted_to (dom f)).
Proof.
move => exte.
apply split_tight => [s | s]; first by rewrite dom_restr_spec => [[]].
by rewrite dom_restr_spec => [[sfdf sfdg]] t fst; split; last apply exte.
Qed.
End tight.

Section tight_comp.
Lemma tight_id_inv S T (f: S ->> T): mf_id \tightens (f\^-1 o f).
Proof.
apply split_tight => [ | s [s' [[t [fst fs't]]] subs]]; first by rewrite F2MF_dom; apply subs_all.
by move => _ <-; split; first by exists t.
Qed.

Arguments tight_id_inv {S} {T} (f).

Lemma tight_comp_l_codom R S T (f f': T ->> R) (g: S ->> T):
	f \tightens (f' \restricted_to (codom g)) -> (f o g) \tightens (f' o g).
Proof.
move => ftf' s [r [[t [gst f'tr]] prop]].
have tfd: t \from dom (f' \restricted_to (codom g)) by exists r; split => //; exists s.
have [r' ftr']:= (ftf' t tfd).1.
have f'tr': f' t r' by apply (ftf' t tfd).2.
split; first exists r'.
	split => [ | t'' gst'']; first by exists t.
	apply ftf'; have [r'' f't''r'']:= prop t'' gst''.
	by exists r''; split => //; exists s.
move => r'' [[t'' [gst'' ft''r'']] prop'].
split => //; exists t''; split => //.
apply ftf'; have [r''' f't''r'']:= prop t'' gst'' => //.
by exists r'''; split => //; exists s.
Qed.

Lemma tight_comp_l R S T (f f': T ->> R) (g: S ->> T):
	f \tightens f' -> (f o g) \tightens (f' o g).
Proof.
move => tight; apply tight_comp_l_codom.
by apply /tight_trans; first apply /tight_restr_w.
Qed.

Lemma cotot_tight_comp_l R S T (f f': T ->> R) (g: S ->> T):
	g \is_singlevalued -> dom f' \is_subset_of codom g -> (f o g) \tightens (f' o g) -> f \tightens f'.
Proof.
move => sing subs tight.
apply split_tight => [t [r ftr] | t [r' f'tr'] r ftr].
	have [ | s gst]:= subs t; first by exists r.
	have sfd: s \from dom (f' o g) by rewrite sing_rcmp => //; exists r; exists t.
	have [r' [[t' [gst' ft'r']] _]]:= tight_dom tight sfd.
	by rewrite (sing s t t') =>//; exists r'.
have [ | s gst]:= subs t; first by exists r'.
have sfd: s \from dom (f' o g) by rewrite sing_rcmp => //; exists r'; exists t.
have subs':= tight_val tight sfd.
have fgsr: f o g s r by rewrite sing_rcmp => //; exists t.
have [[t' [gst' f't'r]]]:= subs' r fgsr.
by rewrite (sing s t t').
Qed.

Lemma tight_comp R S T (f f': T ->> R) (g g': S ->> T):
	f \tightens f' -> g \tightens g' -> (f o g) \tightens (f' o g').
Proof.
intros; apply/tight_trans/tight_comp_l; last by apply H.
apply/tight_trans/tight_comp_r; last by apply H0.
exact/tight_ref.
Qed.

Lemma tight_comp_codom R S T (f f': T ->> R) (g g': S ->> T):
	f \tightens (f' \restricted_to (codom g')) -> g \tightens g' -> (f o g) \tightens (f' o g').
Proof.
move => tight tight'.
apply/tight_trans; first by apply /tight_comp_l_codom/tight.
by apply/tight_trans/tight_comp_r; [apply/tight_ref | apply tight'].
Qed.

Lemma tight_inv_comp R S T (f: S ->> R) (g: T ->> R) (h: S ->> T):
	(f o (h\^-1)) \tightens g -> f \tightens (g o h).
Proof.
move => tight; rewrite -(comp_id_r f).
apply /tight_trans; last apply /tight_comp_r/(tight_id_inv h).
by rewrite -comp_assoc; apply tight_comp_l.
Qed.

Lemma tight_comp_inv R S T (f: S ->> R) (g: T ->> R) (h: S ->> T):
	h \is_surjective_partial_function -> f \tightens (g o h) <-> (f o (h\^-1)) \tightens g.
Proof.
move => [sing /cotot_spec eq]; split => tight; last exact/tight_inv_comp.
rewrite (restr_all g) -eq -comp_id_restr -sing_comp_inv // -comp_assoc.
exact/tight_comp_l.
Qed.
End tight_comp.

Section choice_functions.
Context (S T: Type).
Definition icf S T (g: S -> T) (f: S ->> T) := forall s t, f s t -> f s (g s).
Notation "g '\is_choice_for' f" := (icf g f) (at level 2).

Lemma icf_F2MF_tight (g: S -> T) f:
	g \is_choice_for f <-> (F2MF g) \tightens f.
Proof.
split => [ icf s [] t fst | tight s t fst].
	by split => [ | gs eq ]; [exists (g s) | rewrite -eq; apply: (icf s t)].
have ex: s \from dom f by exists t.
by apply ((tight s ex).2 (g s)).
Qed.

Global Instance icf_prpr: Proper (@eqfun T S ==> @equiv S T ==> iff) (@icf S T).
Proof.
move => f f' fe g g' ge; rewrite !icf_F2MF_tight ge.
by have ->: F2MF f =~= F2MF f' by move => s t /=; rewrite (fe s).
Qed.

Lemma id_icf_inv (f: S ->> T): id \is_choice_for ((f\^-1) o f).
Proof. by move => s s' [[t [fst _]] _]; split; [exists t | exists s]. Qed.

Lemma sing_tot_F2MF_icf (f: S ->> T) g:
	f \is_singlevalued -> f \is_total -> (g \is_choice_for f <-> F2MF g =~= f).
Proof.
move => sing tot.
split => [icf s t| eq s t fst]; last by by rewrite ((eq s t).2 fst).
split => [ eq | fst ]; last by rewrite (sing s t (g s)); last by apply (icf s t fst).
by have [t' fst']:= (tot s); by rewrite -eq; apply (icf s t').
Qed.

Lemma icf_comp R f' (f: T ->> R) g' (g: S ->> T):
	f' \is_choice_for f -> g' \is_choice_for g
		-> (fun s => f' (g' s)) \is_choice_for (f o g).
Proof.
move => icff icfg s r [[t [gst ftr]] prop].
split => [ | t' gst']; last exact (prop t' gst'); exists (g' s).
have gsg's: g s (g' s) by apply/ (icfg s t).
have [r' fg'sr']:= (prop (g' s) gsg's).
by split; last apply/ (icff (g' s) r').
Qed.

Lemma tight_icf (g f: S ->> T):
	g \tightens f -> forall h, (h \is_choice_for g -> h \is_choice_for f).
Proof. by move => tight h icf; apply/icf_F2MF_tight/tight_trans/icf_F2MF_tight/icf. Qed.
End choice_functions.
Notation "f '\is_tightened_by' g" := (tight f g) (at level 2).
Notation "g '\tightens' f" := (tight f g) (at level 2).
Notation "g '\is_choice_for' f" := (icf g f) (at level 2).