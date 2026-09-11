# Capacity Atlas: finite DMC feedback

A Lean proof that noiseless strictly causal output feedback preserves ordinary finite-DMC capacity. At each use, the encoder may use the message and every previous output. The blocklength is fixed in advance; the decoder observes the whole output word. Messages are uniform, error is averaged over messages, and reliable codes exist at every sufficiently large blocklength. There is no input constraint or variable stopping time.

The feedback operational capacity equals the maximum input mutual information in bits, and therefore equals ordinary DMC operational capacity. Ordinary codes embed with identical transition laws, rate, and error. The converse factors off the last use of an arbitrary adaptive policy, applies a sequential entropy inequality, inducts on blocklength, and uses Fano's inequality. The imported finite-simplex theorem supplies a maximizing input.

The Atlas model and reusable APIs are pinned in `lakefile.toml`. `CapacityAtlasFeedback.capacityCertificate` proves `CapacityAtlas.Channel.feedbackCapacityStatement` directly. The audit checks transitive axioms and full canonical-proposition correspondence with rigid universes. Negative controls reject a different proposition and a certificate restricted to smaller universes.

Run `lake --wfail build` and `lake exe capacity_feedback_audit`.

Primary source: C. E. Shannon, [The Zero Error Capacity of a Noisy Channel](https://doi.org/10.1109/TIT.1956.1056798), IRE Transactions on Information Theory IT-2(3), 8–19 (1956), Theorem 6. The finite block model, strictly causal feedback, and ordinary capacity theorem were visually checked in the [Collected Papers reprint](https://www.jonglage.net/theorie/notation/siteswap-avancee/refs/books/Claude%20Shannon%20-%20Collected%20Papers.pdf), printed pages 221 and 232–234. Its natural-log normalization is converted to bits. Our all-sufficiently-large-blocklength direct statement follows from the imported ordinary DMC coding theorem.

AI assistance was used for research, implementation, and review. Human review of statement faithfulness and literature attribution is required before merge.

License: Apache-2.0.
