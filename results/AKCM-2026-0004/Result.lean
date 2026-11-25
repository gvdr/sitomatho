import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.OpenQuotient

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: Topology.IsQuotientMap.of_comp_isQuotientMap (Topology)
-- Step 1: Topology.IsQuotientMap.isCoinducing (Topology)
-- Step 2: Topology.IsCoinducing.continuous (Topology)
-- Step 4: Topology.IsQuotientMap.surjective (Topology)
-- Step 5: Topology.IsOpenEmbedding.of_isEmbedding (Topology)
-- Step 9: Topology.IsOpenEmbedding.toIsEmbedding (Topology)
-- Step 10: Topology.IsEmbedding.isInducing (Topology)
-- Step 11: Topology.IsInducing.isOpenQuotientMap_of_surjective (Topology)
-- Step 12: IsOpenQuotientMap.isOpenMap (IsOpenQuotientMap)
-- Step 13: IsOpenMap.preimage_closure_eq_closure_preimage (IsOpenMap)
theorem akcm_2026_0004
    {X : Type}
    {Y : Type}
    {Z : Type}
    {f : X → Y}
    {g : Y → Z}
    [inst_6 : TopologicalSpace.{0} X]
    [inst_7 : TopologicalSpace.{0} Y]
    [inst_8 : TopologicalSpace.{0} Z]
    (hf : @Topology.IsQuotientMap.{0, 0} X Y inst_6 inst_7 f)
    (hgf : @Topology.IsQuotientMap.{0, 0} X Z inst_6 inst_8
  (@Function.comp.{1, 1, 1} X Y Z g f))
    {u : Set.{0} Z}
    (h_12 : @Topology.IsEmbedding.{0, 0} Y Z inst_7 inst_8 g) :
    @Eq.{1} (Set.{0} Y) (@Set.preimage.{0, 0} Y Z g (@closure.{0} Z inst_8 u))
  (@closure.{0} Y inst_7 (@Set.preimage.{0, 0} Y Z g u)) :=   @IsOpenMap.preimage_closure_eq_closure_preimage.{0, 0} Y Z g inst_7 inst_8
  (@IsOpenQuotientMap.isOpenMap.{0, 0} Y Z inst_7 inst_8 g
    (@Topology.IsInducing.isOpenQuotientMap_of_surjective.{0, 0} Y Z inst_7 inst_8 g
      (@Topology.IsEmbedding.isInducing.{0, 0} Y Z g inst_7 inst_8
        (@Topology.IsOpenEmbedding.toIsEmbedding.{0, 0} Y Z inst_7 inst_8 g
          (@Topology.IsOpenEmbedding.of_isEmbedding.{0, 0} Y Z g inst_7 inst_8 h_12
            (@Topology.IsQuotientMap.surjective.{0, 0} Y Z inst_7 inst_8 g
              (@Topology.IsQuotientMap.of_comp_isQuotientMap.{0, 0, 0} X Y Z f g inst_6 inst_7
                inst_8 hf hgf)))))
      (@Topology.IsQuotientMap.surjective.{0, 0} Y Z inst_7 inst_8 g
        (@Topology.IsQuotientMap.of_comp_isQuotientMap.{0, 0, 0} X Y Z f g inst_6 inst_7 inst_8
          hf hgf))))
  (@Topology.IsCoinducing.continuous.{0, 0} Y Z g inst_7 inst_8
    (@Topology.IsQuotientMap.isCoinducing.{0, 0} Y Z inst_7 inst_8 g
      (@Topology.IsQuotientMap.of_comp_isQuotientMap.{0, 0, 0} X Y Z f g inst_6 inst_7 inst_8 hf
        hgf)))
  u
