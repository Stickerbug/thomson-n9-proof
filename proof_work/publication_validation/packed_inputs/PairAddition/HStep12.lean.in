import PairAddition.Homogeneous
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000
noncomputable section
namespace ThomsonNine.PairAddition
theorem homogeneous_step12 (w d : ℝ) :
    homogeneous 14 w d=2*w*homogeneous 13 w d-d*homogeneous 12 w d := by
  norm_num [homogeneous,qCoefficient,Fin.sum_univ_succ] <;> ring
end ThomsonNine.PairAddition
