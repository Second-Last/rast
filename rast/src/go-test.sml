structure Y =
struct

val _ = OS.Process.exit (Test.main (CommandLine.name (), CommandLine.arguments ()))
    handle _ => OS.Process.exit OS.Process.failure
                            
end
