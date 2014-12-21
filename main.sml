(*~~~~~~~~~~~~~~~~~~~~~~~~~ 
  ~~ HW3 / SML Program 1 ~~
  ~~ Kyle Vickers        ~~
  ~~ cs671               ~~
  ~~~~~~~~~~~~~~~~~~~~~~~~~*)                

(* Modulo:  return the remainder when x is divided by n. 
      Uses only primitive arithmetic operations and comparisons *)

fun modulo( x, n ) = if      x < 0 andalso n > 0   then modNegPos( x, n )
                     else if x > 0 andalso n > 0   then modPosPos( x, n )
                     else if x < 0 andalso n < 0   then modNegNeg( x, n )
                     else                            ~( modPosNeg( ~x, ~n ) )
and modNegPos( x, n ) = if x > n then x
                        else modulo( x + n, n )
and modPosPos( x, n ) = if x < n then x
                        else modulo( x - n, n )
and modNegNeg( x, n ) = if ~x < ~n then x
                        else modulo( x - n, n )
and modPosNeg( x, n ) = if x > n then x
                        else modulo( x + n, n )

(*-- Note the above modulo should work for negative inputs as well, but considering we
     did not have to implement that feature I decided to have the simpler less error 
     prone version below --*)

fun modulo( _,0 ) =  0 (* '' This is the impossible case, just return zero here *)
  | modulo( 0,_ ) =  0
  | modulo( x,n ) = if x < n then x else modulo( x - n, n );



(* Lowest Common Multiple: find the lowest common multiple of two integers 
      In other words, the smallest number evenly divisible by both numers *)

fun lcm( _, 0 ) = 0
  | lcm( 0, _ ) = 0
  | lcm( a, 1 ) = a
  | lcm( 1, b ) = b
  | lcm( a, b ) = if a = b then a else 
    let
      fun lcmH ( a, b, c ) = if (a * b) mod c = 0 then a * b
                             else lcmH( a, b - 1, c )
    in
      lcmH( a, b, b )
    end

(* andEval: Write a logical operator, but do NOT short circuit
            For example, andEval ((fn () => even 3), (fn () -> (print "second"); true))
            causes both even 3 and print "second" to be evaluated, even though 3 is false 
      fn : (unit -> bool) * (unit -> bool) -> bool *)

fun andEval( a, b ) = 
  let
    val aOut = a()
    val bOut = b()
  in 
    if aOut = true andalso bOut = true then true
    else false
  end

(* orEval: Write a logical operator, but do not short circuit... 
           same as andEval with or operator implemented 
      fn : (unit -> bool) * (unit -> bool) -> bool *)

fun orEval( a, b ) = 
  let 
    val aOut = a()
    val bOut = b()
    fun orOp( false, false ) = false
      | orOp( _, _ ) = true
  in
    orOp( aOut, bOut )
  end

(* Out of Order : counts the number of elements in a list which are out of order
                 with  respect to their neighbor, using a given comparison function. 
                 For example nOutOfOrder (op <) [3,2,5,6,1] returns 2 because 3 is 
                 out of order with respect to 2 and 6 is out of order with respect to 1. 
      fn : ((’a * ’a) -> bool) -> ’a list -> int *)



fun nOutOfOrder f l =
  let
    fun ooo f []        = 0
      | ooo f (x::nil)  = 0
      | ooo f (x::y::z) = if not(f( x, y )) then 1 + ( ooo f (y::z) ) 
                          else ( ooo f (y::z) )
  in
      ooo f l 
  end


(* Combinations : write a function combinations such that combinations (n, l) returns
                  a list of all combinations of length n using elements of list l  
  
      fn : (int * ’a list) -> ’a list list  *)

   (* perm and comb share this *)
   fun pc h = fn z => h::z;

fun combinations ( 0, l  ) = [[]]
  | combinations ( n, [] ) = [[]]
  | combinations ( n, l )  =
    let
      fun loop ( 0, l  )   = [[]] 
        | loop ( n, [] )   =  []
        | loop ( n, h::t ) = map (pc h) (loop( n - 1, t ) )@loop( n, t) 
    in
      loop( n, l )                
    end

(* Permutations : Write a function permutations l that returns a list containing 
                  all permutations of list l. 
      fn : ’a list -> ’a list list *)

fun permutations [] = [[]]
  | permutations (h::t) =
    let
      fun position( p, [] )  = [[p]]
        | position( p, h::t) = ( p::h::t )::( List.map ( pc h ) ( position( p,t ) ) )
      val permute_current = fn x => position( h, x ) 
    in
        List.foldr (fn(x,acc) => x @ acc) [] ( List.map permute_current (permutations t) )
    end


(* commonFactors: Finds the prime factors shared by two integers. Each
                  Each factor is represented as a pair ( value, exponent )
                  and the function returns a list of such pairs. No
                  factor should appear more than once in the list and the
                  list is sorted in order of increasing factor values.
                  For instance, commonFactors( 450, 540 ) should return:
                                 [(2,1), (3,2), (5,1)]
                  because 450 = 2*3*3*5*5 and 540 = 2*2*3*3*3*5

         fn : (int * int) -> (int * int) list  *)

fun commonFactors( a, b ) =
  let
    fun factor n =
      let
        fun addFactor _    = []
        fun fac( 0, _, _ ) = []
          | fac( 1, _, _ ) = []
          | fac( x, n, e ) =
              if x mod n = 0 then n::fac( x div n, n, e + 1 )
              else fac( x, n+1, 1 );
      in
        fac( n, 2, 1 )
      end

    fun matching ( l1 : int list, l2 : int list ) =
      let
        fun loop ( [], []    )      = []
          | loop ( h1::_, [] )      = []
          | loop ( [], h2::_ )      = []
          | loop ( h1::t1, h2::t2 ) = case (h1 = h2) of
                                        true => h1::loop( t1, t2 )
                                      | false => (case ( h1 > h2 ) of
                                                    true =>  loop( h1::t1, t2 )
                                                  | false => loop ( t1, h2::t2 ))
      in
        loop ( l1, l2 )
      end

    fun count( []   : int list )   = 0
      | count( h::t : int list )   =
      let
        val head = h;
        fun loop ( _, []   : int list   ) = 0
          | loop ( n, h::t : int list   ) = if n = h then 1 + loop( n, t )
                                            else loop( n, t )
      in
        loop (head, h::t)
      end

    fun countList []       = []
      | countList (h::t)   =
      let
        fun loop ( n, [] ) =  []
          | loop ( n, h::t  ) =  if n = 1 then (count (h::t))::loop( (count(h::t)), t )
                                          else loop( n - 1, t )
      in
        loop ( 1, h::t )
      end

    fun getExponents []       = []
      | getExponents (h::t)   =
      let
        fun loop ( n, [] ) =  []
          | loop ( n, h::t  ) =  if n = 1 then (count (h::t))::loop( (count(h::t)), t )
                                          else loop( n - 1, t )
      in
        loop ( 1, h::t )
      end

    fun getNumbers [] : int list = []
      | getNumbers ( h::[] : int list ) = h::getNumbers([])
      | getNumbers ( h::t  : int list ) = if h = hd(t) then getNumbers t
                                          else h::getNumbers(t);

    fun toTuples( numList, expList ) = ListPair.zip ( numList, expList );

    val facs1 = factor a
    val facs2 = factor b
    val matches = matching ( facs1, facs2 )
    val exps = countList matches
    val nums = getNumbers matches
  in
    toTuples( nums, exps )
  end

(* Best Align:  Takes two strings and attempts to find the best alignment of their
                contents to achieve the longest match. It may skip as many spaces
                as it likes before beginning acutlaly matching the string's contents.
                It does not liit itself to exact matches, but allows the inserver of
                a * character to replaces non-matched characteres. Each of these errors
                causes the algorithm to count as 1 less than its previous length
                ( so "*histle" is counted as length 5.) The function returns the 
                overlapped text of the best-length match ( accounting for the cost
                of errors ) and the number of shifts required to start it. Negative
                values for number of shifts indicate that the second string was shifted
                rather than the first.

            Example : input  > bestAlign "these cats are a menace" "cats ate mice" 
                      output > ("cats a*e ", ~6 ) 

         fun bestAlign str1 str2 =        fn : string -> string -> string * int            *)

fun bestAlign str1 str2 = 
    let
      fun comp( [], _, isShifted, score, shifts ) = []
        | comp( _, [], isShifted, score, shifts ) = []
        | comp( h1::t1, h2::t2, isShifted, score, shifts ) =  if h1 = h2 then (score + 1, h1, shifts)::comp( t1, t2, true, score + 1, shifts )                                
                                                              else if isShifted then (score - 2, #"*", shifts)::comp(t1,t2,true, score - 2, shifts )
                                                              else comp( h1::t1, t2, false, score, shifts + 1 );
      fun highestFarthest( [], score, i, I ) = I
        | highestFarthest( h::t : ( int * char * int ) list, score, i, I ) = if #1(h) >= score then highestFarthest( t , #1(h), i+1, i )
                                                                             else highestFarthest( t, score, i+1, I )
      fun removeExcess( [], _ ) = []
        | removeExcess( l, i )  = List.take( l, i + 1 )

      fun peelChars  [] = []
        | peelChars  ( h::t : ( int * char * int ) list ) = #2( h )::peelChars( t )
              handle List.Empty => [] 

      fun peelScores [] = []
        | peelScores  ( h::t : ( int * char * int) list ) = #1( h )::peelScores( t )
              handle List.Empty => [] 

      fun peelShifts [] = []
        | peelShifts ( h::t : ( int * char * int ) list ) = #3( h )::peelShifts( t )
              handle List.Empty => [] 
     
      val ex1 = String.explode str1;                   
      val ex2 = String.explode str2;                     
      val l1 = comp( ex1, ex2, false, 0, 0 );            
      val l2 = comp( ex2, ex1, false, 0, 0 );               
      val matchWithScoreShiftData1 = removeExcess( l1, (highestFarthest(l1,0,0,0 )));
      val matchWithScoreShiftData2 = removeExcess( l2, (highestFarthest(l2,0,0,0 )));
      val finalCharList1 = peelChars( matchWithScoreShiftData1 );
      val finalCharList2 = peelChars( matchWithScoreShiftData2 );
      val final_CL1_Shifts = hd( peelShifts l1 ) handle List.Empty => 0;
      val final_CL2_Shifts = ~1 * hd( peelShifts l2 ) handle List.Empty => 0; 
      val firstBest  = ( String.implode( finalCharList1 ), final_CL1_Shifts )      
      val secondBest = ( String.implode( finalCharList2 ), final_CL2_Shifts )      
    in
      if String.size (#1firstBest) > String.size (#1secondBest) then firstBest
      else secondBest
    end


(* Print Align: Prints two strings and their matched content on subsequent lines,
                padding with the correct number of spaces to show the alignment.
                Nevative values for shift indicate that the second string should be
                shifted.

        Example: input  > printAlign "these cats are a menace" "cats ate mice" "cats a*e " ~6 
                 output > these cats are a menace
                                cats ate mice
                                cats a*e                                                   
                fn : string -> string -> string -> int -> ()     *)

  local
    val SP = #" " ;
    val RE = #"\n";

    fun makeSpace 0 = []
      | makeSpace n = if (n>0) then (#" ")::makeSpace( n-1 ) else (#" ")::makeSpace( n+1 );

    fun construct s1 s2 s3 s = if s > 0 then (makeSpace s)@(String.explode s1)@[RE]    
                                                          @(String.explode s2)@[RE]    
                                                          @(String.explode s3)@[RE]
                                        else
                                                           (String.explode s1)@[RE]    
                                            @(makeSpace s)@(String.explode s2)@[RE]    
                                            @(makeSpace s)@(String.explode s3)@[RE];

    fun printCharList charlist = List.app (fn s => (if s = RE then (print("\n"))  else(print(Char.toCString s)))) charlist;

  in
    fun printAlign str1 str2 str3 shift = printCharList( construct str1 str2 str3 shift )
  end;


