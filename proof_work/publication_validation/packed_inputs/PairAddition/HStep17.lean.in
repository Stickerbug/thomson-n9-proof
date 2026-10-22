import PairAddition.Homogeneous
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
theorem homogeneous_step17 (w d : ℝ) :
    homogeneous 19 w d=2*w*homogeneous 18 w d-d*homogeneous 17 w d := by
  norm_num [homogeneous,qCoefficient,Fin.sum_univ_succ] <;> ring
end ThomsonNine.PairAddition
