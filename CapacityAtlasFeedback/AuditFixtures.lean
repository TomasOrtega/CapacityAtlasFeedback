/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasFeedback

namespace CapacityAtlasFeedback.AuditFixtures

/-- This valid theorem deliberately omits the canonical universe generality. -/
theorem universeZeroCertificate {X Y : Type} [Fintype X] [Fintype Y]
    [Nonempty X] (channel : CapacityAtlas.FiniteChannel X Y) :
    CapacityAtlas.Channel.feedbackCapacityStatement channel :=
  CapacityAtlasFeedback.capacityCertificate channel

end CapacityAtlasFeedback.AuditFixtures
