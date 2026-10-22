import MainCoverage.RootData
import MainCoverage.CutCover

namespace ThomsonNine.PackedMain
structure CertifiedChunk where
  path : List Bool
  tree : Tree
  certificate : pathOK rootState path=true ∧ check axisLookup localCores (atPath rootState path) tree=true
end ThomsonNine.PackedMain
