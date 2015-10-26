
structure Main =
struct
  val thy = the_context ();

  fun your_tac s n b = HCTactic.my_tac (thm s) n b

end;
