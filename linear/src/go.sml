structure X =
struct

val _ = OS.Process.exit (Top.main (CommandLine.name (), CommandLine.arguments ()))
    handle _ => OS.Process.exit OS.Process.failure
                            
end
