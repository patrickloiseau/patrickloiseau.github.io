 
let make name ext = (name,ext)

let name (filename,ext) = filename
let ext  (filename,ext) = ext

let filename (name,ext) = if ext="" then name else name ^ "." ^ ext 

							  
let output_in (name,ext) str =
  let output_filename = filename (name,ext)
  in let 
      channel_out = open_out output_filename
  in
    begin
      print_string ("\n.....data written in: " ^ output_filename ^ "\n");
      output_string channel_out str ;
      close_out channel_out 
    end
      
      

