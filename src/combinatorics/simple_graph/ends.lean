import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory

--local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           [∀ x y : V, nonempty (G.walk x y)]
           [has_inter (finset V)]
           [decidable_eq  V]
           [has_compl V]
           [locally_finite G]


def connected_outside (K : set V) (x y : V) : Prop :=
  ∃ w : walk G x y, disjoint K w.support.to_finset

namespace connected_outside

def c_o := connected_outside G

lemma monotone {K K' : set V} (hK : K ⊆ K') (x y : V) :
  c_o G K' x y → c_o G K x y :=
λ ⟨w,dis⟩, ⟨w,disjoint_of_subset_left hK dis⟩

lemma not_in  {K : set V} {x y : V} (conn : c_o G K x y) : x ∉ K ∧ y ∉ K  :=
begin
  rcases conn with ⟨xy, dis⟩,
  have x_in : x ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.start_mem_support},
  have y_in : y ∈ ↑(xy.support.to_finset),
    by {rw [mem_coe, list.mem_to_finset], apply walk.end_mem_support},
  exact ⟨set.disjoint_right.mp dis x_in,set.disjoint_right.mp dis y_in⟩,
end

@[protected]
lemma refl {K : set V} (x : V) (hx : x ∉ K) : c_o G K x x :=
⟨walk.nil, by { rw [walk.support_nil,list.to_finset_cons,list.to_finset_nil],simpa only [insert_emptyc_eq, coe_singleton, set.disjoint_singleton_right],}⟩

lemma of_adj_outside (K : set V) (x y : V) (hx : x ∉ K) (hy : y ∉ K) :
  G.adj x y → c_o G K x y :=
begin
  intro a,
  use (walk.cons a walk.nil),
  rw [walk.support_cons,walk.support_nil,list.to_finset_cons,list.to_finset_cons,list.to_finset_nil],
  simp only [insert_emptyc_eq, coe_insert, coe_singleton],
  rw [set.disjoint_iff_inter_eq_empty,
      set.inter_comm,
      set.insert_inter_of_not_mem hx,
      set.singleton_inter_eq_empty.mpr hy],
end

@[protected]
lemma symm  {K : set V} : symmetric (c_o G K) :=
λ x y, λ ⟨w,dis⟩, ⟨w.reverse, by {rw [walk.support_reverse,list.to_finset_reverse],exact dis}⟩

@[protected]
lemma trans {K : set V} : transitive (c_o G K)
| x y z ⟨xy,disxy⟩ ⟨yz,disyz⟩ :=
begin
  use xy.append yz,
  rw walk.support_append,
  rw list.to_finset_append,
  simp only [coe_union, set.disjoint_union_right],
  refine ⟨disxy,_⟩,
  { have : ↑(yz.support.tail.to_finset) ⊆ ↑(yz.support.to_finset), by
    { rw walk.support_eq_cons, simp, rw finset.coe_insert, exact set.subset_insert y (↑(yz.support.tail.to_finset)),},
    apply @set.disjoint_of_subset_right V K ↑(yz.support.tail.to_finset) ↑(yz.support.to_finset) this,
    exact disyz,}
end


end connected_outside









open simple_graph.connected_outside

def components (K : set V) : set (set V) := {C : set V | ∃ x ∈ C, C = {y : V | c_o G K x y}}

namespace component

variable (K : set V)

def of (x : V) : (set V) := {y : V | c_o G K x y}

lemma of_in_components (x : V) (hx : x ∉ K) : of G K x ∈ components G K :=
⟨x,connected_outside.refl G x hx,rfl⟩

lemma mem_of (x : V) (hx : x ∉ K) : x ∈ (of G K x) := connected_outside.refl G x hx

lemma nempty (C : set V) : C ∈ components G K → set.nonempty C
| ⟨x,x_in_C,sat⟩ := ⟨x,x_in_C⟩

lemma is_c_o (C : set V) : C ∈ components G K →  ∀ x y ∈ C, c_o G K x y
| ⟨z,z_in,eq⟩ x x_in y y_in :=
begin
  rw eq at x_in y_in,
  exact connected_outside.trans G (connected_outside.symm G x_in) y_in,
end

lemma not_in_of_in_comp (C : set V) (hC : C ∈ components G K) (x : V) (hx : x ∈ C) : x ∉ K :=
(not_in G (is_c_o G K C hC x hx x hx)).1

lemma conn_sub (P : set V)
  (Pnempty : set.nonempty P) (P_c_o : ∀ x y ∈ P, c_o G K x y) :
  ∃ C : set V, C ∈ components G K ∧ P ⊆ C :=
begin
  rcases Pnempty with ⟨p,p_in_P⟩,
  have p_notin_K : p ∉ K := (not_in G (P_c_o p p_in_P p p_in_P)).1,
  let p_in_Cp := mem_of G K p p_notin_K,
  use [of G K p, of_in_components G K p p_notin_K],
  rw set.subset_def,
  exact λ x x_in_P, P_c_o p p_in_P x x_in_P,
end



-- This one could probably use `conn_sub` but I'm too lazy/stupid to figure the neatest way to do things
lemma eq_of_common_mem (C D : set V) (hC : C ∈ components G K) (hD : D ∈ components G K)
  (x : V) (x_in_C : x ∈ C) (x_in_D : x ∈ D) : C = D :=
begin
  rcases hC with ⟨y,y_in_C,rfl⟩,
  rcases hD with ⟨z,z_in_D,rfl⟩,
  apply set.ext,
  intro w,
  have y_c_o_z : c_o G K y z, from connected_outside.trans G x_in_C (connected_outside.symm G x_in_D),
  split,
  from λ w_in_C, connected_outside.trans G (connected_outside.symm G y_c_o_z) w_in_C,
  from λ w_in_D, connected_outside.trans G y_c_o_z w_in_D,
end

lemma mem_of_mem_of_conn (C : set V) (hC : C ∈ components G K)
  (x y : V) (x_in_C : x ∈ C) (x_conn_y : c_o G K x y) : y ∈ C :=
begin
  rcases hC with ⟨c,c_in_C,rfl⟩,
  exact connected_outside.trans G x_in_C x_conn_y,
end

lemma mem_of_mem_of_adj (C : set V) (hC : C ∈ components G K)
  (x y : V) (x_in_C : x ∈ C) (y_notin_K : y ∉ K) (adj : G.adj x y) : y ∈ C :=
mem_of_mem_of_conn G K C hC x y x_in_C $ of_adj_outside G K x y (not_in_of_in_comp G K C hC x x_in_C) y_notin_K adj


lemma conn_sub_unique (P : set V)
  (Pnempty : set.nonempty P) (P_c_o : ∀ x y ∈ P, c_o G K x y) : ∃! C : set V, C ∈ components G K ∧ P ⊆ C :=
begin
  rcases conn_sub G K P Pnempty P_c_o with ⟨C,⟨C_comp,P_sub_C⟩⟩,
  use C,
  split,
  exact ⟨C_comp,P_sub_C⟩,
  rintros D ⟨D_comp,P_sub_D⟩,
  rcases Pnempty with ⟨p,p_in_P⟩,
  exact (eq_of_common_mem G K C D C_comp D_comp p (P_sub_C p_in_P) (P_sub_D p_in_P)).symm,
end

lemma sub_of_conn_intersects
  (P : set V) (Pnempty : set.nonempty P) (P_c_o : ∀ x y ∈ P, c_o G K x y)
  (C ∈ components G K) (inter : (P ∩ C).nonempty) : P ⊆ C :=
begin
  sorry -- todo
end

lemma walk_outside_is_contained (C : set V) (hC : C ∈ components G K) :
  Π (x y : V), Π (w : G.walk x y), x ∈ C → y ∈ C → disjoint K w.support.to_finset → (w.support.to_finset : set V) ⊆ C
| x _ nil             hx hy _  := by {simp only [support_nil, list.to_finset_cons, list.to_finset_nil, insert_emptyc_eq, coe_singleton, set.singleton_subset_iff],exact hx}
| x y (@cons V G _ z _ adj tail) hx hy hw := by {
  rw [walk.support,list.to_finset_cons],
  simp only [coe_insert],
  rw set.insert_subset,
  split,
  exact hx,
  have : z ∈ (cons adj tail).support.to_finset, by simp only [support_cons, list.to_finset_cons, finset.mem_insert, list.mem_to_finset, start_mem_support, or_true],
  have : z ∉ K, from set.disjoint_right.mp hw this,
  have : z ∈ C, from mem_of_mem_of_adj G K C hC x z hx ‹z∉K› adj,
  have : disjoint K tail.support.to_finset, {
    apply set.disjoint_of_subset_right _ hw,
    simp only [support_cons, list.to_finset_cons, coe_insert, set.subset_insert],
  },
  exact walk_outside_is_contained z y tail ‹z∈C› hy this,
}


lemma is_connected (C : set V) (hC : C ∈ components G K) (x y : V) (hx : x ∈ C) (hy : y ∈ C) :
  ∃ w : G.walk x y, (w.support.to_finset : set V) ⊆ C :=
begin
  rcases is_c_o G K C hC x hx y hy with ⟨w,dis_K⟩,
  exact ⟨w,walk_outside_is_contained G K C hC x y w hx hy dis_K⟩,
end



--only used in next lemma
private def walks (C : set V) (k : V) := Σ (x : C), G.walk x k
private def w_len  (C : set V) (k : V) :  walks G C k → ℕ := λ w, w.2.length
private def w_min (C : set V) (k : V) := @function.argmin _ _ (w_len G C k) _ nat.lt_wf
private def w_min_spec (C : set V) (k : V) := @function.argmin_le _ _ (w_len G C k) _ nat.lt_wf

lemma adjacent_to (Knempty: K.nonempty) (C : set V) (hC : C ∈ components G K) :
∃ (v k : V), k ∈ K ∧ v ∈ C ∧ G.adj k v :=
begin
  rcases Knempty with ⟨k,k_in_K⟩,
  have nemptywalks : nonempty (walks G C k), by {
    rcases nempty G K C hC with ⟨x,x_in_C⟩,
    have w : G.walk x k := sorry, -- it's in the hypotheses!!
    exact nonempty.intro ⟨⟨x,x_in_C⟩,w⟩,},
  rcases hhh : @w_min V G _ _ _ _ _ C k nemptywalks with ⟨x, min_walk⟩,
  have x_notin_K : x.val ∉ K, from (not_in G (is_c_o G K C hC x.val x.prop x.val x.prop)).1,
  rcases min_walk with nil|⟨_,y,_,x_adj_y,y_walk_k⟩,
  { exfalso,
    have : c_o G K x x, from is_c_o G K C hC x.val x.prop x.val x.prop,
    exact x_notin_K k_in_K,},
  { by_cases h : y ∈ K,
    { use x, use y, use h, use x.prop, exact (x_adj_y).symm,},
    { have : c_o G K x y, from connected_outside.of_adj_outside G K x y x_notin_K h x_adj_y,
      have : y ∈ C, from mem_of_mem_of_conn G K C hC x.val y x.prop this,
      let subwalk : walks G C k := ⟨⟨y,this⟩,y_walk_k⟩,
      have min_is_min := @w_min_spec V G _ _ _ _ _ C k subwalk (nemptywalks),
      have len_subwalk : (w_len G C k subwalk) + 1 = w_len G C k (@w_min V G _ _ _ _ _ C k nemptywalks), by {
        unfold w_len at *,
        rw [hhh,←simple_graph.walk.length_cons],
      },
      have : (w_len G C k subwalk) < (w_len G C k subwalk) + 1, from lt_add_one (w_len G C k subwalk),
      rw len_subwalk at this,
      exfalso,
      haveI : nonempty (walks G C k), by sorry,
      have ok : argmin (w_len G C k) nat.lt_wf = w_min G C k, by simpa, -- can I do this without simpa?
      rw ok at min_is_min,
      exact (lt_iff_not_ge _ _).mp this min_is_min,},}
end

def bdry : set V := {x : V | x ∉ K ∧ ∃ k ∈ K, G.adj x k}
lemma bdry_subset_union_neighbors : (bdry G K: set V) ⊆ set.Union (λ x : K, G.neighbor_set x) :=
begin
  unfold bdry,
  rw set.subset_def,
  rintros x ⟨not_in_K,k,k_in_K,adj⟩,
  rw set.mem_Union,
  exact ⟨⟨k,k_in_K⟩,adj.symm⟩,
end

lemma bdry_finite (Kfin : K.finite) : (bdry G K).finite :=
begin
  apply set.finite.subset _ (bdry_subset_union_neighbors G K),
  apply set.finite.sUnion,
  haveI : fintype ↥K, from finite.fintype Kfin,
  apply set.finite_range,
  rintros nbd ⟨k,k_to_nbd⟩,
  simp only at k_to_nbd,
  rw k_to_nbd.symm,
  exact finite.intro (_inst_5 ↑k), -- lol thanks library_search
end

def to_bdry_point (Knempty: K.nonempty) (Kfinite: K.finite) : components G K → V :=
λ C, some $ adjacent_to G K Knempty C.val C.prop

def to_bdry_point_spec (Knempty: K.nonempty) (Kfinite: K.finite) (C : components G K) :
  let v := (to_bdry_point G K Knempty Kfinite C) in ∃ k : V, k ∈ K ∧ v ∈ C.val ∧ G.adj k v :=
some_spec (adjacent_to G K Knempty C.val C.prop)

lemma to_bdry_point_inj (Knempty: K.nonempty) (Kfinite: K.finite) :
  function.injective $ to_bdry_point G K Knempty Kfinite :=
begin
  rintros C D c_eq_d,
  rcases to_bdry_point_spec G K Knempty Kfinite C with ⟨k,kK,cC,k_adj_c⟩,
  rcases to_bdry_point_spec G K Knempty Kfinite D with ⟨l,lK,dD,l_adj_d⟩,
  exact subtype.eq ( eq_of_common_mem G K C.val D.val C.prop D.prop _ cC (c_eq_d.symm ▸ dD)),
end

lemma to_bdry_point_in_bdry  (Knempty: K.nonempty) (Kfinite: K.finite) :
  range (to_bdry_point G K Knempty Kfinite) ⊆ bdry G K :=
begin
  rw set.subset_def,
  rintros _ ⟨C,rfl⟩,
  rcases to_bdry_point_spec G K Knempty Kfinite C with ⟨k,kK,cC,k_adj_c⟩,
  have := not_in_of_in_comp G K C.val C.prop _ cC,
  exact ⟨this,⟨k,⟨kK,k_adj_c.symm⟩⟩⟩,
end

lemma finite (Knempty: K.nonempty) (Kfinite: K.finite) : (components G K).finite :=
begin
  by_contra comps_inf,
  haveI : infinite (subtype (components G K)), from infinite_coe_iff.mpr comps_inf,
  have := @set.infinite_range_of_injective (subtype (components G K)) V (_inst) (to_bdry_point G K Knempty Kfinite) (to_bdry_point_inj G K Knempty Kfinite),
  have : (bdry G K).infinite, from set.infinite.mono (to_bdry_point_in_bdry G K Knempty Kfinite) this,
  exact this (bdry_finite G K Kfinite),
end


end component







def inf_components (K : set V) := {C : set V | C ∈ components G K ∧ C.infinite}

section inf_components

variables {K L L' M : set V}
          (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)
          (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)


lemma inf_components_subset (K : set V) : inf_components G K ⊆ components G K := λ C h, h.1

instance inf_components_finite (Knempty: K.nonempty) (Kfinite: K.finite) :
  fintype (inf_components G K) := (set.finite.subset (component.finite G K Knempty Kfinite) (inf_components_subset G K)).fintype

def component_is_still_conn (D : set V) (D_comp : D ∈ components G L) :
  ∀ x y ∈ D, c_o G K x y :=
λ x xD y yD, connected_outside.monotone G K_sub_L x y (component.is_c_o G L D D_comp x xD y yD)


def bwd_map : inf_components G L → inf_components G K :=
λ D,
let
  itexists := component.conn_sub G
              K D.val
              (component.nempty G L D.val D.prop.1)
              (component_is_still_conn G K_sub_L D.val D.prop.1)
, C := some itexists
, C_prop := some_spec itexists
in
  ⟨C,C_prop.1, λ fin, D.prop.2 (set.finite.subset fin C_prop.2)⟩


def bwd_map_def (D : inf_components G L) (C : inf_components G K) :
  bwd_map G K_sub_L D = C ↔ D.val ⊆ C.val :=
let
  itexists := component.conn_sub G K D (component.nempty G L D.val D.prop.1) (component_is_still_conn G K_sub_L D.val D.prop.1),
  C' := some itexists,
  C_prop' := some_spec itexists
in
  begin
    have eqdef : bwd_map G K_sub_L D =
           ⟨C',C_prop'.1, λ fin, D.prop.2 (set.finite.subset fin C_prop'.2)⟩, by
    { unfold bwd_map, dsimp,simpa,},
    split,
    { intro eq, cases eq, exact C_prop'.2,},
    { intro sub,
      have lol := component.conn_sub_unique G K D (component.nempty G L D.val D.prop.1) (component_is_still_conn G K_sub_L D.val D.prop.1), -- the fact that D is still connected wrt K … should be easy
      rcases lol with ⟨uniqueC,uniqueC_is_good,unicity⟩,
      rw eqdef,
      apply subtype.ext_val, simp,
      rw (unicity C' C_prop'),
      rw (unicity C.val ⟨C.prop.1,sub⟩).symm,simp,
    }
  end

def bwd_map_sub (D : inf_components G L) : D.val ⊆ (bwd_map G K_sub_L D).val :=
begin
  apply (bwd_map_def G K_sub_L D (bwd_map G K_sub_L D)).mp,
  reflexivity,
end

lemma bwd_map_refl (C : inf_components G K) : bwd_map G (set.subset.refl K) C = C :=
by {rw bwd_map_def}

lemma subcomponents_cover (K_sub_L : K ⊆ L) (C : set V) (hC : C ∈ components G K) :
  C ⊆ L ∪ (⋃₀ { D : set V | D ∈ components G L ∧ D ⊆ C}) :=
begin
  rintro x x_in_C,
  by_cases h: x∈L,
  { left,exact h},
  { right,
    let D := component.of G L x,
    have : x ∈ D, from component.mem_of G L x h,
    rw set.mem_sUnion,
    use D,
    split,
    { split,
      exact component.of_in_components G L x h,
      let D_comp := component.of_in_components G L x h,
      exact component.sub_of_conn_intersects G K D
        (component.nempty G L D D_comp)
        (component_is_still_conn G K_sub_L D D_comp)
        C hC ( set.nonempty_inter_iff_exists_left.mpr ⟨⟨x,‹x∈D›⟩,x_in_C⟩  : (D ∩ C).nonempty),
    },
    from component.mem_of G L x h,
  }
end

lemma bwd_map_surjective
  (Knempty : K.nonempty) (Kfinite : K.finite)
  (Lnempty : L.nonempty) (Lfinite : L.finite)
  : surjective (bwd_map G K_sub_L) :=
begin
  unfold surjective,
  rintros ⟨C,C_comp,C_inf⟩,
  let L_comps := components G L,
  let L_comps_in_C := { D : set V | D ∈ components G L ∧ D ⊆ C},
  have sub : L_comps_in_C ⊆ L_comps, from (λ D ⟨a,b⟩,  a),
  have : L_comps_in_C.finite, from set.finite.subset (component.finite G L Lnempty Lfinite) sub,
  have : (⋃₀ L_comps_in_C).infinite, from
    λ fin, C_inf ((Lfinite.union fin).subset (subcomponents_cover G K_sub_L C C_comp)),

  have : ∃ D : set V, D ∈ L_comps_in_C ∧ D.infinite, by {
    by_contra' all_fin,
    simp at all_fin,
    exact this ( set.finite.sUnion
                 ‹L_comps_in_C.finite›
                 ( λ D ⟨D_comp,D_sub_C⟩, all_fin D D_comp D_sub_C) ),},
  rcases this with ⟨D,⟨D_comp_L,D_sub_C⟩,D_inf⟩,
  use ⟨D,D_comp_L,D_inf⟩,
  rw (bwd_map_def G K_sub_L ⟨D,D_comp_L,D_inf⟩ ⟨C,C_comp,C_inf⟩),
  exact D_sub_C,
end


def bwd_map_comp :
  (bwd_map G K_sub_L) ∘ (bwd_map G L_sub_M) = (bwd_map G (K_sub_L.trans L_sub_M)) :=
begin
  apply funext,
  rintro E,
  let D := bwd_map G L_sub_M E,
  let C := bwd_map G K_sub_L D,
  apply eq.symm,
  unfold function.comp,
  apply (bwd_map_def G (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G L_sub_M E).trans (bwd_map_sub G K_sub_L D),
end

def bwd_map_comp' (E : inf_components G M) :
  bwd_map G K_sub_L (bwd_map G L_sub_M E) = bwd_map G (K_sub_L.trans L_sub_M) E :=
begin
  let D := bwd_map G L_sub_M E,
  let C := bwd_map G K_sub_L D,
  apply eq.symm,
  apply (bwd_map_def G (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G L_sub_M E).trans (bwd_map_sub G K_sub_L D),
end

def bwd_map_diamond (E : inf_components G M) :
  bwd_map G K_sub_L (bwd_map G L_sub_M E) = bwd_map G K_sub_L' (bwd_map G L'_sub_M E) :=
by rw [bwd_map_comp',bwd_map_comp']

end inf_components

section ends

variables {K L L' M : set V}
          (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)
          (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)



private def finsubsets := {K : set V | K.finite}

private def up (K : @finsubsets V _ _ _) := {L ∈ @finsubsets V _ _ _ | K.val ⊆ L}
private lemma up_sub  (K : finsubsets)  : up K ⊆ @finsubsets V _ _ _ := λ K H, H.1
private lemma in_up  (K : @finsubsets V _ _ _) : K.val ∈ (up K) := ⟨K.prop,set.subset.refl K.val⟩
private lemma up_cofin  (K : @finsubsets V _ _ _) :
  ∀ M : @finsubsets V _ _ _, ∃ L : up K, M.val ⊆ L := λ M,
begin
  use ⟨M.val ∪ K.val, set.finite.union M.prop K.prop, set.subset_union_right M.val K.val⟩,
  exact set.subset_union_left M.val K.val,
end




private structure fam :=
  (fam: set (set V))
  (fin: fam ⊆ finsubsets)
  (cof: ∀ K : @finsubsets V _ _ _, ∃ F : fam, K.val ⊆ F)
private def fin_fam : fam := ⟨@finsubsets V _ _ _,set.subset.refl _,(λ K, ⟨K,set.subset.refl _⟩)⟩
private def fin_fam_up (K : @finsubsets V _ _ _) : fam := ⟨up K,up_sub K, up_cofin K⟩




def ends_for (ℱ : @fam V _ _ _) :=
{ f : Π (K : ℱ.1), inf_components G K.val | ∀ K L : ℱ.1, ∀ h : K.val ⊆ L.val, bwd_map G h (f L) = (f K) }

lemma ends_for_directed  (ℱ : @fam V _ _ _)
  (g : ends_for G ℱ) (K L : ℱ.1) :
  ∃ (F : ℱ.1) (hK : K.val ⊆ F.val) (hL : L.val ⊆ F.val),
    g.1 K = bwd_map G hK (g.1 F) ∧ g.1 L = bwd_map G hL (g.1 F) :=
begin
  rcases (ℱ.cof ⟨K.val∪L.val,set.finite_union.mpr ⟨(ℱ.fin K.prop),(ℱ.fin L.prop)⟩⟩) with ⟨F,F_good⟩,
  use F,
  use (set.subset_union_left K.val L.val).trans F_good,
  use (set.subset_union_right K.val L.val).trans F_good,
  split;
  { apply eq.symm,
    apply g.2,}
 end

def ends := ends_for G (@fin_fam V _ _ _)



def to_ends_for (ℱ : fam) : ends G → ends_for G ℱ :=
λ f : ends G, ⟨ λ K, f.1 ⟨K, ℱ.fin K.property⟩
                , λ K L hKL, f.2 (set.inclusion ℱ.fin K) (set.inclusion ℱ.fin L) hKL⟩

def to_ends_for_def (ℱ : fam) (e : ends G) (K : ℱ.fam) :
  e.val (⟨K.val,mem_of_subset_of_mem ℱ.fin K.prop⟩ : finsubsets) = (to_ends_for G ℱ e).val K := refl _



def of_ends_for (ℱ : fam) : ends_for G ℱ → ends G :=
λ g,
  let
    f : Π (K : finsubsets), inf_components G K.val := λ K,
      let
        F := classical.some (ℱ.cof K)
      , K_sub_F := classical.some_spec (ℱ.cof K)
      in
        bwd_map G K_sub_F (g.1 F)
  , f_comm : ∀ K L : finsubsets, ∀ h : K.val ⊆ L.val, bwd_map G h (f L) = (f K) := λ K L hKL, by
    { --simp *,
      let FK := some (ℱ.cof K),
      let K_FK := some_spec (ℱ.cof K),
      let FL := some (ℱ.cof L),
      let L_FL := some_spec (ℱ.cof L),
      rcases ends_for_directed G ℱ H ℱ.cof g FK FL with ⟨M,FK_M,FL_M,backK,backL⟩,
      have hey : f K = bwd_map G K_FK (g.1 FK), by simpa,
      have hoo : f L = bwd_map G L_FL (g.1 FL), by simpa,
      rw [hey,hoo,backK,backL,bwd_map_comp',bwd_map_comp',bwd_map_comp'],}
  in
    ⟨f,f_comm⟩

-- Thanks Kyle Miller
def equiv_ends_for (ℱ : fam) : ends G ≃ ends_for G ℱ :=
{ to_fun := to_ends_for G ℱ,
  inv_fun := of_ends_for G ℱ,
  left_inv := begin
    rintro ⟨g, g_comm⟩,
    simp only [of_ends_for, to_ends_for, comp_app, id.def, subtype.mk_eq_mk],
    ext1 F,
    apply g_comm,
  end,
  right_inv := begin
    rintro ⟨g, g_comm⟩,
    simp only [of_ends_for, to_ends_for, comp_app, id.def, subtype.mk_eq_mk],
    ext1 F,
    apply g_comm,
  end }


lemma ends_empty_graph : is_empty V → is_empty (ends G) :=
begin
  rintros ⟨no_V⟩,
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  rcases f ⟨∅,set.finite_empty⟩ with ⟨_,⟨b,_⟩,_⟩,
  exact no_V b,
end

lemma ends_finite_graph  (Vfinite : (@set.univ V).finite) : is_empty (ends G) :=
begin
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  rcases f ⟨@set.univ V,Vfinite⟩ with ⟨C,⟨_,_⟩,C_inf⟩,
  exact C_inf (set.finite.subset Vfinite (set.subset_univ C)),
end


def eval_for (ℱ : fam) (K : ℱ.fam):
  ends_for G ℱ → inf_components G K := λ e, e.val K


def eval (K : @finsubsets V _ _ _): ends G → inf_components G K := eval_for G fin_fam K


def eval_comm  (ℱ : fam) (K : ℱ.fam) (e : ends G) :
  eval_for G ℱ K (equiv_ends_for G ℱ e) = @eval V G _ _ _ _ _ ⟨K.val,ℱ.fin K.prop⟩ e :=
begin
  simp only [eval, eval_for, equiv_ends_for, equiv.coe_fn_mk],
  rw [←to_ends_for_def],
end



lemma eval_injective_for_up (K : finsubsets)
  (inj_from_K : ∀ L : @finsubsets V _ _ _, K.val ⊆ L.val → injective (bwd_map G ‹K.val⊆L.val›)) :
  injective (eval_for G (fin_fam_up K) ⟨K,in_up K⟩) :=
begin
  rintros e₁ e₂,
  simp only [eval_for, subtype.val_eq_coe],
  rintro same,
  apply subtype.eq,
  ext1 L,
  simp only [subtype.val_eq_coe],
  apply inj_from_K ⟨L.val,L.prop.1⟩ L.prop.2,
  rw [e₁.prop ⟨K.val,in_up K⟩ L L.prop.2,e₂.prop ⟨K.val,in_up K⟩ L L.prop.2],
  assumption,
end

lemma eval_injective (K : finsubsets)
  (inj_from_K : ∀ L : @finsubsets V _ _ _, K.val ⊆ L.val → injective (bwd_map G ‹K.val⊆L.val›)) :
  injective (eval G K) :=
begin
  rintros e₁ e₂ same,
  let f₁ := (equiv_ends_for G (fin_fam_up K)) e₁,
  let f₂ := (equiv_ends_for G (fin_fam_up K)) e₂,
  have : f₁ = f₂, by {
    apply eval_injective_for_up G K inj_from_K,
    rw [ eval_comm G (fin_fam_up K) ⟨K,in_up K⟩ e₁,
         eval_comm G (fin_fam_up K) ⟨K,in_up K⟩ e₂],
    dsimp only,
    have lol : K = ⟨↑K,K.2⟩, by simp,
    rw lol at same,
    exact same,
  },
  simpa only [embedding_like.apply_eq_iff_eq],
end


structure nat_fam :=
  (f : ℕ → set V)
  (zero : (f 0).nonempty)
 -- (fin : ∀ n, (f n) ∈ finsubsets V)
  (mon: ∀ m  n, m ≤ n → f m ⊆ f n)
  (cof: ∀ K : @finsubsets V _ _ _, ∃ n : ℕ, K.val ⊆ f n)


def nat_fam_to_fam  (nf : @nat_fam V _ _ _) : @fam V _ _ _ := sorry

lemma extend_along (nf : @nat_fam V _ _ _) (C : inf_components G (nf.f 0)) :
  Π i : ℕ, inf_components G (nf.f i) :=
nat.rec
  (by {exact C})
  (λ k extend_along_k, some $ bwd_map_surjective G (fmon k (k+1) (nat.le_succ k))
                              (set.nonempty.mono (fmon 0 k $ nat.zero_le k) Knempty)
                              (f k).prop
                              (set.nonempty.mono (fmon 0 (k+1) $ nat.zero_le $ k+1) Knempty)
                              (f $ k + 1).prop
                              (extend_along_k))


lemma extend_along_comm_add (f : ℕ → @finsubsets V _ _ _) (fmon: ∀ m  n, m ≤ n → (f m).val ⊆ (f n).val)
  (Knempty : (f 0).val.nonempty) (Kfinite : (f 0).val.finite) (C : inf_components G (f 0)) :
let e := extend_along G f fmon Knempty Kfinite C in
  ∀ (i j : ℕ), (bwd_map G $ fmon i (i+j) (nat.le_add_right _ _)) (e (i+j)) = e i :=
let e := extend_along G f fmon Knempty Kfinite C in
λ i, @nat.rec
  (λ j, (bwd_map G $ fmon i (i+j) (nat.le_add_right _ _)) (e (i+j)) = e i)
  (by {apply bwd_map_refl,})
  (λ j hj, by {rw ←hj,sorry})

lemma extend_along_comm (f : ℕ → @finsubsets V _ _ _) (fmon: ∀ m  n, m ≤ n → (f m).val ⊆ (f n).val)
  (Knempty : (f 0).val.nonempty) (Kfinite : (f 0).val.finite) (C : inf_components G (f 0)) :
let
  e := extend_along G f fmon Knempty Kfinite C
in
  ∀ i j, i ≤ j → (bwd_map G $ fmon i j ‹i≤j›) (e j) = e i :=
begin
  rintros A i j ilej, -- not sure why I have to introduce this A before the rest ?!
  rcases le_iff_exists_add.mp ilej with ⟨k,hk⟩,
  have lol := extend_along_comm_add G f fmon Knempty Kfinite C i k,
  -- I want to do rewrites but I cannot!!!
  sorry,
end

lemma extend_along_spec (f : ℕ → @finsubsets V _ _ _) (fmon: ∀ m  n, m ≤ n → (f m).val ⊆ (f n).val)
  (Knempty : (f 0).val.nonempty) (Kfinite : (f 0).val.finite) (C : inf_components G (f 0)) :
extend_along G f fmon Knempty Kfinite C 0 = C := by {sorry} -- should be by def ??

lemma extend_along_fam
  (f : ℕ → @finsubsets V _ _ _)
  (fmon: ∀ m  n, m ≤ n → (f m).val ⊆ (f n).val)
  (fcof: ∀ K : @finsubsets V _ _ _, ∃ n : ℕ, K.val ⊆ f n)
  (Knempty : (f 0).val.nonempty) (Kfinite : (f 0).val.finite) (C : inf_components G (f 0)) :
  end_for

/-
def enum_fam_def
  (enum : ℕ ≃ V) -- this assumption is consequence of connected + locally finite anyway
  (Knempty : K.nonempty) (Kfinite : K.finite) (C : inf_components G K) : ℕ → @finsubsets V _ _ _ :=
  λ n, ⟨K ∪ enum '' {j | j < n}, sorry⟩

lemma enum_fam_zero
  (enum : ℕ ≃ V) -- this assumption is consequence of connected + locally finite anyway
  (Knempty : K.nonempty) (Kfinite : K.finite) (C : inf_components G K) :
  (enum_fam_def G enum Knempty Kfinite C 0).val = K :=
begin
  unfold enum_fam_def,simp,
end

lemma enum_fam_mono
  (enum : ℕ ≃ V) -- this assumption is consequence of connected + locally finite anyway
  (Knempty : K.nonempty) (Kfinite : K.finite) (C : inf_components G K) :
  ∀ (i j : ℕ), i ≤ j → (enum_fam_def G enum Knempty Kfinite C i).val ⊆ (enum_fam_def G enum Knempty Kfinite C j).val :=
λ i j ilej, set.union_subset_union (subset_refl K) (set.image_subset _ (λ n nlei, le_trans (by {simp at nlei,exact nlei}) ilej))

lemma enum_fam_cof
  (enum : ℕ ≃ V) -- this assumption is consequence of connected + locally finite anyway
  (Knempty : K.nonempty) (Kfinite : K.finite) (C : inf_components G K) :
  ∀ F : finsubsets, ∃ n : ℕ, F.val ⊆ (enum_fam_def G enum Knempty Kfinite C n).val :=
begin
  rintros ⟨F,Ffin⟩,
  have : ∃ M : ℕ, enum.inv_fun '' F ⊆ {j : ℕ | j < M}, by sorry,
  rcases this with ⟨M,Mbound⟩,
  use M,
  simp,
  rintros v vF,
  have : v ∈ enum.to_fun '' {j : ℕ | j < M}, by sorry,
  exact set.mem_union_right K this,
end

def enum_fam  (enum : ℕ ≃ V) -- this assumption is consequence of connected + locally finite anyway
  (Knempty : K.nonempty) (Kfinite : K.finite) : fam = ⟨enum_fam_def enum Knempty Kfinite, ⟩
-/


lemma of_component
  (enum : ℕ ≃ V) -- this assumption is consequence of connected + locally finite anyway
  (Knempty : K.nonempty) (Kfinite : K.finite) (C : inf_components G K) :
  ∃ e : (ends G), (e.val (⟨K,Kfinite⟩ : finsubsets)).val = C.val :=
begin

  let fenum_fam := enum_fam G enum Knempty Kfinite C,
  let fenum_fam_cof := enum_fam_cof G enum Knempty Kfinite C,
  let fenum_fam_mono := enum_fam_mono G enum Knempty Kfinite C,
  have lol := (enum_fam_zero G enum Knempty Kfinite C).symm,
  let fe := extend_along G fenum_fam fenum_fam_mono (lol ▸ Knempty) (lol ▸ Kfinite) (sorry /- lol ▸ c-/),
  let e : ends_for

  /-

  use extend_along on this function
  get an element of ends_for and an element of ends
  -/
end

/-
example (K : set V) (Knempty : K.nonempty) (Kfinite : K.finite)
        (maxcard : ∀ L : finsubsets, K ⊆ L.val →
                   fintype (inf_components G L) ≤ fintype.card (inf_components G K) ) :

-/

--lemma ends_eq_disjoints_ends_of (Knempty : K.nonempty) (Kfinite : K.finite) : ends G = disjoint union of the ends of G-K



end ends

-- theorem `card_components_mon` saying htat `λ K, card (inf_components G K)` is monotone
-- theorem `finite_ends_iff` saying that `ends` is finite iff the supremum `λ K, card (inf_components G K)` is finite
-- theorem `finite_ends_card_eq` saying that if `ends` is finite, the cardinality is the sup
-- theorem `zero_ends_iff` saying that `ends = ∅` iff `V` is finite



end simple_graph
