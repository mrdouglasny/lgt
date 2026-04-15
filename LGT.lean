-- Lattice Gauge Theory in Lean 4
-- Discrete differential geometry, Wilson action, mass gap

-- Layer 1: Discrete geometry (cell complex, forms, d/d*)
import LGT.Lattice.CellComplex
import LGT.Lattice.DiscreteForms
import LGT.Lattice.DiscreteExteriorDerivative

-- Layer 2: Gauge fields (connections on lattice, holonomy)
import LGT.GaugeField.Connection
import LGT.GaugeField.GaugeTransformation
import LGT.GaugeField.Holonomy

-- Layer 3: Wilson action and observables
import LGT.WilsonAction.PlaquetteAction
import LGT.WilsonAction.WilsonLoop
import LGT.WilsonAction.GaugeInvariance

-- Layer 4: Mass gap (2D proof via Doeblin)
import LGT.MassGap.TransferMatrix
import LGT.MassGap.DoeblinCondition
import LGT.MassGap.MassGap2D

-- Layer 5: Gibbs specification + Dobrushin (d≥3 mass gap path)
import LGT.Gibbs.YMSpec
import LGT.Gibbs.YMDobrushin
import LGT.Gibbs.YMIsGibbs
