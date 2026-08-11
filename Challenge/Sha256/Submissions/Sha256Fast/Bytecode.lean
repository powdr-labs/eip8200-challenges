import Challenge.Sha256.Submissions.Sha256Fast.Proofs.Rounds8

namespace Challenge.Sha256.Submissions.Sha256Fast

/-- The exact 2,622-byte loop-of-eight artifact proved below.  `Loop.bytes` is
assembled from the generated, typed instruction list; the submission checker
independently compares it byte-for-byte with `bytecode.hex`. -/
def bytecode : ByteArray := Loop.bytes

end Challenge.Sha256.Submissions.Sha256Fast
