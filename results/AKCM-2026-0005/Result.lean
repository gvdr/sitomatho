import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

-- Step 0: OpenPartialHomeomorph.continuousOn_extend (OpenPartialHomeomorph)
-- Step 2: ContinuousOn.continuousAt (ContinuousOn)
-- Step 5: ContinuousAt.tendsto (ContinuousAt)
-- Step 6: Filter.Tendsto.mapClusterPt (Filter)
-- Step 7: MapClusterPt.clusterPt (MapClusterPt)
-- Step 8: ClusterPt.neBot (ClusterPt)
theorem akcm_2026_0005
    {x_1 : Type}
    {E : Type}
    {M : Type}
    {H : Type}
    [inst_5 : NontriviallyNormedField.{0} x_1]
    [inst_6 : NormedAddCommGroup.{0} E]
    [inst_7 : @NormedSpace.{0, 0} x_1 E (@NontriviallyNormedField.toNormedField.{0} x_1 inst_5)
  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} E inst_6)]
    [inst_8 : TopologicalSpace.{0} H]
    [inst_9 : TopologicalSpace.{0} M]
    (f : @OpenPartialHomeomorph.{0, 0} M H inst_9 inst_8)
    {I : @ModelWithCorners.{0, 0, 0} x_1 inst_5 E inst_6 inst_7 H inst_8}
    {u : M}
    (h_13 : @Membership.mem.{0, 0} (Set.{0} M) (Filter.{0} M) (@Filter.instMembership.{0} M)
  (@nhds.{0} M inst_9 u)
  (@PartialEquiv.source.{0, 0} M E
    (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7
      inst_8 inst_9 f I))) :
    @Filter.NeBot.{0} E
  (@min.{0} (Filter.{0} E) (@Filter.instInf.{0} E)
    (@nhds.{0} E
      (@UniformSpace.toTopologicalSpace.{0} E
        (@PseudoMetricSpace.toUniformSpace.{0} E
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} E
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} E inst_6))))
      (@PartialEquiv.toFun.{0, 0} M E
        (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7
          inst_8 inst_9 f I)
        u))
    (@Filter.map.{0, 0} M E
      (@PartialEquiv.toFun.{0, 0} M E
        (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7
          inst_8 inst_9 f I))
      (@nhds.{0} M inst_9 u))) :=   @ClusterPt.neBot.{0} E
  (@UniformSpace.toTopologicalSpace.{0} E
    (@PseudoMetricSpace.toUniformSpace.{0} E
      (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} E
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} E inst_6))))
  (@PartialEquiv.toFun.{0, 0} M E
    (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8 inst_9 f
      I)
    u)
  (@Filter.map.{0, 0} M E
    (@PartialEquiv.toFun.{0, 0} M E
      (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8 inst_9 f
        I))
    (@nhds.{0} M inst_9 u))
  (@MapClusterPt.clusterPt.{0, 0} E
    (@UniformSpace.toTopologicalSpace.{0} E
      (@PseudoMetricSpace.toUniformSpace.{0} E
        (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} E
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} E inst_6))))
    M (@nhds.{0} M inst_9 u)
    (@PartialEquiv.toFun.{0, 0} M E
      (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8 inst_9 f
        I))
    (@PartialEquiv.toFun.{0, 0} M E
      (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8 inst_9 f
        I)
      u)
    (@Filter.Tendsto.mapClusterPt.{0, 0} E
      (@UniformSpace.toTopologicalSpace.{0} E
        (@PseudoMetricSpace.toUniformSpace.{0} E
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} E
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} E inst_6))))
      M (@nhds.{0} M inst_9 u)
      (@PartialEquiv.toFun.{0, 0} M E
        (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8 inst_9
          f I))
      (@PartialEquiv.toFun.{0, 0} M E
        (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8 inst_9
          f I)
        u)
      (@nhds_neBot.{0} M inst_9 u)
      (@ContinuousAt.tendsto.{0, 0} M E inst_9
        (@UniformSpace.toTopologicalSpace.{0} E
          (@PseudoMetricSpace.toUniformSpace.{0} E
            (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} E
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} E inst_6))))
        (@PartialEquiv.toFun.{0, 0} M E
          (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8
            inst_9 f I))
        u
        (@ContinuousOn.continuousAt.{0, 0} M E inst_9
          (@UniformSpace.toTopologicalSpace.{0} E
            (@PseudoMetricSpace.toUniformSpace.{0} E
              (@SeminormedAddCommGroup.toPseudoMetricSpace.{0} E
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} E inst_6))))
          (@PartialEquiv.toFun.{0, 0} M E
            (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8
              inst_9 f I))
          (@PartialEquiv.source.{0, 0} M E
            (@OpenPartialHomeomorph.extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6 inst_7 inst_8
              inst_9 f I))
          u
          (@OpenPartialHomeomorph.continuousOn_extend.{0, 0, 0, 0} x_1 E M H inst_5 inst_6
            inst_7 inst_8 inst_9 f I)
          h_13))))
