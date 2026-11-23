(* Build Munta's muntax checker with Poly/ML instead of MLton.
   The files and their order are those of ML/muntax.mlb at the pinned commit.
   ML/Mlton_Main.sml is left out: it only calls main() under MLton, and
   polyc calls main itself. MUNTA_ML names the directory with Munta's ML sources. *)
val dir = valOf (OS.Process.getEnv "MUNTA_ML");
fun u f = use (dir ^ "/" ^ f);
val _ = app u ["Unsynchronized.sml", "Writeln.sml", "Simple_Model_Checker.sml",
               "basics.ML", "library.ML", "Unsynchronized.sml", "Util.sml", "Muntax.sml"];
