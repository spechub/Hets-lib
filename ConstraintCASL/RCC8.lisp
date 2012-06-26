  (def-calculus "Relative distance calculus (reldistcalculus)"
    :arity :binary
    :identity-relation __EQ__
    :converse-operation ((NTPPi NTPP))

    :base-relations (__DC__ __EC__ __PO__ __NTPP__ __TPP__ ...)
    :composition-operation ((DC EC (DC EC PO TPP NTPP))
  (same closer (same closer farther))
  (same farther (same closer farther))
  (closer same (same closer farther))
  (closer closer (same closer farther))
  (closer farther (same closer farther))
  (farther same (same closer farther))
  (farther closer (same closer farther))
  (farther farther (same closer farther))))

