:- module(pure_output,
	  [ phrase_to_file/2		% :Grammar, +File
	  ]).
:- use_module(library(error)).

/** <module> Pure, phrase based output to files

This module is part of pio.pl,   dealing with _pure_ _output_:

@tbd	Provide support for alternative output writers
@tbd	Support non-repositioning streams, such as sockets and pipes.
@tbd  Are there better ways to committing?
@author Ulrich Neumerkel
@author Jan Wielemaker
*/

%%	phrase_to_file(:Grammar, +File) is nondet.
% The string described by grammer is written to File.
% File is only created, when Grammar is determinate or when
% a solution is comitted.

:- module_transparent
	phrase_to_file/2.

phrase_to_file(Grammar, File) :-
	strip_module(Grammar, M, G),
	absolute_file_name(File, AbsoluteFile),
	tmp_file(pio, TmpFile),
	setup_and_call_cleanup(open(TmpFile,write,Stream),
		 (  Solution = yes,
		    pure_output:write_output_stream(Codes, Stream, Finished),
		 	 phrase(M:G,Codes)
		 ),
		 pure_output:close_lazystream(Solution, Finished, TmpFile, AbsoluteFile, Stream)).

write_output_stream(Codes, Stream, Finished) :-
	stream_property(Stream, position(Pos)),
	freeze(Codes, output_stream_to_output(Pos, Codes, Stream, Finished)).

:- op(950,fy, [$]).
$(X) :-
	copy_term_nat(X,Y),numbervars(Y,0,_),portray_clause(call:Y),
	(	  call_cleanup(X, Det = true)
	*->  copy_term_nat(X,Z),numbervars(Z,0,_),
	  	  (	Det == true
	  	  ->  portray_clause(detexit:Z),
	  	  		!
	  	  ;	portray_clause(ndetexit:Z)
	  	  )
	;	  !,
		  copy_term_nat(X,Z),numbervars(Z,0,_),
	  	  portray_clause(nosol:Z),
		  fail
	).
$(X) :-
	  copy_term_nat(X,Y),numbervars(Y,0,_),portray_clause(fail:Y),
	  fail.

output_stream_to_output(Pos0, Codes0, Stream, Finished) :-
	$must_be(list_or_partial_list, xy),
	set_stream_position(Stream, Pos0),
	$write_partial_codes(Codes0, Codes1, Stream),
%	put_partial_codes(Stream, _, Codes0, Codes1),
	stream_property(Stream, position(Pos1)),
	% Idealiter truncate file to current position now
	$must_be(list_or_partial_list, Codes1),
	(	var(Codes1)
	-> freeze(Codes1, output_stream_to_output(Pos1, Codes1, Stream, Finished))
	;	Codes1 = []
	->	Finished = true
	;	Codes1 = [Code|_],
		(	var(Code)
		->	freeze(Code, output_stream_to_output(Pos1, Codes1, Stream, Finished))
		;	type_error(codes,Codes1)
		)
	).

close_lazystream(Solution, Finished, TmpFile, AbsoluteFile, Stream) :-
	(	var(Solution)
	->	close(Stream),
		delete_file(TmpFile)
	;	var(Finished)
	->	close(Stream),
		delete_file(TmpFile),
		representation_error(unfinished_output)
	;	stream_property(Stream, position(Pos)),
		% truncate_to_position(Stream,Pos),
		close(Stream),
		% rename_file(TmpFile, AbsoluteFile),
		Pos = '$stream_position'(_, _, _, Bytes),
		format(atom(Codes),'head -c ~d ~a > ~a',[Bytes, TmpFile, AbsoluteFile]),
		(	shell(Codes)
		->	delete_file(TmpFile)
		;	delete_file(TmpFile),
			permission_error(execute, command, Codes)
		)
	).



% maybe put this into C

write_partial_codes(Codes0, Codes, _) :-
	var(Codes0), !,
	Codes0 = Codes.
write_partial_codes([Code|Codes0], Codes, Stream) :-
	nonvar(Code), !,
	put_code(Stream, Code),
	write_partial_codes(Codes0, Codes, Stream).
write_partial_codes(Codes, Codes, _Stream).
