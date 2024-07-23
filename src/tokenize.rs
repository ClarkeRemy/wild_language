use logos::Logos;

#[derive(Logos,Debug, PartialEq)]
pub(crate) enum Token{
  #[token(":")]  Col        ,
  #[token(".")]  Dot        ,
  #[token("_")]  Underbar   ,
  #[token("`")]  Tick       ,
  #[token(":?")] MatchRec   ,
  
  #[regex(r" +\.\. *")] Update,
  #[regex(r":: +")]    Def      ,
  #[regex(r" +:= +")]    Newtype  ,
  #[regex(r" +:\| +")] MatchGuard ,
  #[regex(r" +: +")]   Alias   ,
  #[regex(r"\?\{ *")]  Match   ,
  #[regex(r"\\\{ *")]  Lambda  ,
  #[regex(r",\( *")]   Tuple   ,
  #[regex(r"\{ *")]    CurlyL  , // Set
  #[regex(r" *\}")]    CurlyR  ,
  #[regex(r"\( *")]    RoundL  , 
  #[regex(r" *\)")]    RoundR  ,
  #[regex(r"\[ *")]    SquareL ,
  #[regex(r" *\]")]    SquareR ,

  #[regex(r"(0|[1-9][0-9]*)\{ *", priority = 4)]         Elements,
  #[regex(r" +")]                         Space  ,
  #[regex(r"( *\n *)+")]                  Newline,
  #[regex(r#""(\\"|[^"])*""#)]           StrLit ,
  #[regex(r"(?x)
           ([0-9]+([.:][0-9]+)*
           |[0-9]+((\.\.|::)[0-9]+)*
           |[0-9]+((\.\.\.|:::)[0-9]+)*
           )
           ([0-9]+([.:][0-9]+)*
           |[0-9]+((\.\.|::)[0-9]+)*
           |[0-9]+((\.\.\.|:::)[0-9]+)*
           |[^()\[\]{}`_.:\s0-9]
           )*
         ", priority = 5)]                           NumLit   ,
  #[regex(r"[^()\[\]\.{}`_:\s]*")]     Id       ,

  // comments are ":#", for now comments are striped
  #[error]#[regex(r"(\n|\t| )+:# [^\n]*", logos::skip)] Error
}

#[cfg(test)] mod test{
    use super::*;

  #[test] fn trival(){
    let example = r#"




    "#;

    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    print_tokens(example,lex)
    // for e in lex.spanned() {println!("{e:?},")};
  }

  #[test]fn numeric_literals(){
    let example = r#"

      0-
      7,3,4,5
      1,000,000.47-
      0<1;2;3>
      0..1
      0..70.double
      0..70
      3:5
      45::78
      45...6
      45:::78
      +_5_7-+5i
      +_8_5..5.double

    "#;
    use Token::*;
    let expected = [
      (Newline, 0..8),(NumLit, 8..10),
      (Newline, 10..17),(NumLit, 17..24),
      (Newline, 24..31),(NumLit, 31..44),
      (Newline, 44..51),(NumLit, 51..59),
      (Newline, 59..66),(NumLit, 66..70),
      (Newline, 70..77),(NumLit, 77..82),(Dot, 82..83),(Id, 83..89),
      (Newline, 89..96),(NumLit, 96..101),
      (Newline, 101..108),(NumLit, 108..111),
      (Newline, 111..118),(NumLit, 118..124),
      (Newline, 124..131),(NumLit, 131..137),
      (Newline, 137..144),(NumLit, 144..151),
      (Newline, 151..158),(Id, 158..159),(Underbar, 159..160),(NumLit, 160..161),(Underbar, 161..162),(NumLit, 162..167),
      (Newline, 167..174),(Id, 174..175),(Underbar, 175..176),(NumLit, 176..177),(Underbar, 177..178),(NumLit, 178..182),(Dot, 182..183),(Id, 183..189),
      (Newline, 189..195)
    ];
    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    lex.spanned().zip(expected.into_iter()).for_each(|(input,ex)|assert_eq!(input,ex));
    // for e in lex.spanned() {println!("{e:?},")};
    // print_tokens(example,lex)
  }

  #[test]fn alias_and_newtype(){
    let example = r#"

      :# relational algebra on types?
      g : {a b c}
      G := {a b c}
      j : {b c d}
      J := {b c d}
      k : union_g_j        :# <=> {a b c d e}
      l : intersection:g:j :# <=> {b c}
      m : anti-join:g:j    :# <=> {a}
      l : {g j}            :# <=> union_g_j   :# auto flattening
      L : {G J}            :# <=> {G J}       :# G and J are named, so they do not flatten
      t : {G g}            :# <=> {G a b c}   :# note g will flatten

    "#;
    use Token::*;
    let expected = [
      (Newline, 39..46),(Id, 46..47),(Alias, 47..50),(CurlyL, 50..51),(Id, 51..52),(Space, 52..53),(Id, 53..54),(Space, 54..55),(Id, 55..56),(CurlyR, 56..57),
      (Newline, 57..64),(Id, 64..65),(Newtype, 65..69),(CurlyL, 69..70),(Id, 70..71),(Space, 71..72),(Id, 72..73),(Space, 73..74),(Id, 74..75),(CurlyR, 75..76),
      (Newline, 76..83),(Id, 83..84),(Alias, 84..87),(CurlyL, 87..88),(Id, 88..89),(Space, 89..90),(Id, 90..91),(Space, 91..92),(Id, 92..93),(CurlyR, 93..94),
      (Newline, 94..101),(Id, 101..102),(Newtype, 102..106),(CurlyL, 106..107),(Id, 107..108),(Space, 108..109),(Id, 109..110),(Space, 110..111),(Id, 111..112),(CurlyR, 112..113),
      (Newline, 113..120),(Id, 120..121),(Alias, 121..124),(Id, 124..129),(Underbar, 129..130),(Id, 130..131),(Underbar, 131..132),(Id, 132..133),
      (Newline, 159..166),(Id, 166..167),(Alias, 167..170),(Id, 170..182),(Col, 182..183),(Id, 183..184),(Col, 184..185),(Id, 185..186),
      (Newline, 199..206),(Id, 206..207),(Alias, 207..210),(Id, 210..219),(Col, 219..220),(Id, 220..221),(Col, 221..222),(Id, 222..223),
      (Newline, 237..244),(Id, 244..245),(Alias, 245..248),(CurlyL, 248..249),(Id, 249..250),(Space, 250..251),(Id, 251..252),(CurlyR, 252..253),
      (Newline, 302..309),(Id, 309..310),(Alias, 310..313),(CurlyL, 313..314),(Id, 314..315),(Space, 315..316),(Id, 316..317),(CurlyR, 317..318),
      (Newline, 393..400),(Id, 400..401),(Alias, 401..404),(CurlyL, 404..405),(Id, 405..406),(Space, 406..407),(Id, 407..408),(CurlyR, 408..409),
      (Newline, 462..468)
    ];
    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    lex.spanned().zip(expected.into_iter()).for_each(|(input,ex)|assert_eq!(input,ex));    
    // for e in lex.spanned() {println!("{e:?}")};
    // print_tokens(example,lex)
  }
  #[test]fn set_and_subset_notation(){
    let example = r#"

      Option:'T := 1{Some:'T None}
      
      zeros :: v3_{x_0 y_0 x_0}
      a :: {x_5 .. zeros}:v3
      j (:: {int char}) {'5' 0}

      
      (vec3 := {
        x := u16
        y := u16
        z := u16
      })
      
      vec3 := {x y z}
      
      x := u16
      y := u16
      z := u16
      vec3 := {x y z}
      
      v :: v3_{x_5 y_7 z_9}
      
      (swap :: ?{
        val : v3_{x_a y_b ..} :: {y_a x_b .. val}:v3
      })
      swap :: ?{ v3_{x_a y_b z_c} :: v3_{y_a x_b z_c} }

    "#;
    use Token::*;
    let expected = [
      (Newline, 0..8),(Id, 8..14),(Col, 14..15),(Id, 15..17),(Newtype, 17..21),(Elements, 21..23),(Id, 23..27),(Col, 27..28),(Id, 28..30),(Space, 30..31),(Id, 31..35),(CurlyR, 35..36),
      (Newline, 36..50),(Id, 50..55),(Space, 55..56),(Def, 56..59),(Id, 59..61),(Underbar, 61..62),(CurlyL, 62..63),(Id, 63..64),(Underbar, 64..65),(NumLit, 65..66),(Space, 66..67),(Id, 67..68),(Underbar, 68..69),(NumLit, 69..70),(Space, 70..71),(Id, 71..72),(Underbar, 72..73),(NumLit, 73..74),(CurlyR, 74..75),
      (Newline, 75..82),(Id, 82..83),(Space, 83..84),(Def, 84..87),(CurlyL, 87..88),(Id, 88..89),(Underbar, 89..90),(NumLit, 90..91),(Update, 91..95),(Id, 95..100),(CurlyR, 100..101),(Col, 101..102),(Id, 102..104),
      (Newline, 104..111),(Id, 111..112),(Space, 112..113),(RoundL, 113..114),(Def, 114..117),(CurlyL, 117..118),(Id, 118..121),(Space, 121..122),(Id, 122..126),(CurlyR, 126..127),(RoundR, 127..128),(Space, 128..129),(CurlyL, 129..130),(Id, 130..133),(Space, 133..134),(NumLit, 134..135),(CurlyR, 135..136),
      (Newline, 136..151),(RoundL, 151..152),(Id, 152..156),(Newtype, 156..160),(CurlyL, 160..161),
      (Newline, 161..170),(Id, 170..171),(Newtype, 171..175),(Id, 175..178),
      (Newline, 178..187),(Id, 187..188),(Newtype, 188..192),(Id, 192..195),
      (Newline, 195..204),(Id, 204..205),(Newtype, 205..209),(Id, 209..212),
      (Newline, 212..219),(CurlyR, 219..220),(RoundR, 220..221),
      (Newline, 221..235),(Id, 235..239),(Newtype, 239..243),(CurlyL, 243..244),(Id, 244..245),(Space, 245..246),(Id, 246..247),(Space, 247..248),(Id, 248..249),(CurlyR, 249..250),
      (Newline, 250..264),(Id, 264..265),(Newtype, 265..269),(Id, 269..272),
      (Newline, 272..279),(Id, 279..280),(Newtype, 280..284),(Id, 284..287),
      (Newline, 287..294),(Id, 294..295),(Newtype, 295..299),(Id, 299..302),
      (Newline, 302..309),(Id, 309..313),(Newtype, 313..317),(CurlyL, 317..318),(Id, 318..319),(Space, 319..320),(Id, 320..321),(Space, 321..322),(Id, 322..323),(CurlyR, 323..324),
      (Newline, 324..338),(Id, 338..339),(Space, 339..340),(Def, 340..343),(Id, 343..345),(Underbar, 345..346),(CurlyL, 346..347),(Id, 347..348),(Underbar, 348..349),(NumLit, 349..350),(Space, 350..351),(Id, 351..352),(Underbar, 352..353),(NumLit, 353..354),(Space, 354..355),(Id, 355..356),(Underbar, 356..357),(NumLit, 357..358),(CurlyR, 358..359),
      (Newline, 359..373),(RoundL, 373..374),(Id, 374..378),(Space, 378..379),(Def, 379..382),(Match, 382..384),
      (Newline, 384..393),(Id, 393..396),(Alias, 396..399),(Id, 399..401),(Underbar, 401..402),(CurlyL, 402..403),(Id, 403..404),(Underbar, 404..405),(Id, 405..406),(Space, 406..407),(Id, 407..408),(Underbar, 408..409),(Id, 409..410),(Update, 410..413),(CurlyR, 413..414),(Space, 414..415),(Def, 415..418),(CurlyL, 418..419),(Id, 419..420),(Underbar, 420..421),(Id, 421..422),(Space, 422..423),(Id, 423..424),(Underbar, 424..425),(Id, 425..426),(Update, 426..430),(Id, 430..433),(CurlyR, 433..434),(Col, 434..435),(Id, 435..437),
      (Newline, 437..444),(CurlyR, 444..445),(RoundR, 445..446),
      (Newline, 446..453),(Id, 453..457),(Space, 457..458),(Def, 458..461),(Match, 461..464),(Id, 464..466),(Underbar, 466..467),(CurlyL, 467..468),(Id, 468..469),(Underbar, 469..470),(Id, 470..471),(Space, 471..472),(Id, 472..473),(Underbar, 473..474),(Id, 474..475),(Space, 475..476),(Id, 476..477),(Underbar, 477..478),(Id, 478..479),(CurlyR, 479..480),(Space, 480..481),(Def, 481..484),(Id, 484..486),(Underbar, 486..487),(CurlyL, 487..488),(Id, 488..489),(Underbar, 489..490),(Id, 490..491),(Space, 491..492),(Id, 492..493),(Underbar, 493..494),(Id, 494..495),(Space, 495..496),(Id, 496..497),(Underbar, 497..498),(Id, 498..499),(CurlyR, 499..500),(CurlyR, 500..502),
      (Newline, 502..508)
    ];
    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    lex.spanned().zip(expected.into_iter()).for_each(|(input,ex)|assert_eq!(input,ex));    
    // for e in lex.spanned() {println!("{e:?}")};
    // print_tokens(example,lex)
  }
  #[test]fn generic_params(){
    let example = r#"

      [1 2 3]:(vec:num) . 0 fold +



      b : box:(1{tensor:num tensor:char})
      [[2 3]:b 
       ["hey" "bro"]
      ]:tensor:b
      
      v : vec:num
      [4 5]:v
      
      a : array:3:num
      [5 6]:a
      
      a : array:2:(v : vec:num)
      [[1 2 3]:v
       [5 6 7]
      ]:a
      
      v : vec:(a : array:3:num)
      [[1 2 3]:a
       [4 5 6]
      ]:v
      
      v : vec:(vec:num)
      [[num]]:v1
      
      [num]:vec:num
      
      [num]:array:3:num
      [num]:vec:num
      [num]:tensor

    "#;
    use Token::*;
    let expected = [
      (Newline, 0..8),(SquareL, 8..9),(NumLit, 9..10),(Space, 10..11),(NumLit, 11..12),(Space, 12..13),(NumLit, 13..14),(SquareR, 14..15),(Col, 15..16),(RoundL, 16..17),(Id, 17..20),(Col, 20..21),(Id, 21..24),(RoundR, 24..25),(Space, 25..26),(Dot, 26..27),(Space, 27..28),(NumLit, 28..29),(Space, 29..30),(Id, 30..34),(Space, 34..35),(Id, 35..36),
      (Newline, 36..46),(Id, 46..47),(Alias, 47..50),(Id, 50..53),(Col, 53..54),(RoundL, 54..55),(Elements, 55..57),(Id, 57..63),(Col, 63..64),(Id, 64..67),(Space, 67..68),(Id, 68..74),(Col, 74..75),(Id, 75..79),(CurlyR, 79..80),(RoundR, 80..81),
      (Newline, 81..88),(SquareL, 88..89),(SquareL, 89..90),(NumLit, 90..91),(Space, 91..92),(NumLit, 92..93),(SquareR, 93..94),(Col, 94..95),(Id, 95..96),
      (Newline, 96..105),(SquareL, 105..106),(StrLit, 106..111),(Space, 111..112),(StrLit, 112..117),(SquareR, 117..118),
      (Newline, 118..125),(SquareR, 125..126),(Col, 126..127),(Id, 127..133),(Col, 133..134),(Id, 134..135),
      (Newline, 135..149),(Id, 149..150),(Alias, 150..153),(Id, 153..156),(Col, 156..157),(Id, 157..160),
      (Newline, 160..167),(SquareL, 167..168),(NumLit, 168..169),(Space, 169..170),(NumLit, 170..171),(SquareR, 171..172),(Col, 172..173),(Id, 173..174),
      (Newline, 174..188),(Id, 188..189),(Alias, 189..192),(Id, 192..197),(Col, 197..198),(NumLit, 198..199),(Col, 199..200),(Id, 200..203),
      (Newline, 203..210),(SquareL, 210..211),(NumLit, 211..212),(Space, 212..213),(NumLit, 213..214),(SquareR, 214..215),(Col, 215..216),(Id, 216..217),
      (Newline, 217..231),(Id, 231..232),(Alias, 232..235),(Id, 235..240),(Col, 240..241),(NumLit, 241..242),(Col, 242..243),(RoundL, 243..244),(Id, 244..245),(Alias, 245..248),(Id, 248..251),(Col, 251..252),(Id, 252..255),(RoundR, 255..256),
      (Newline, 256..263),(SquareL, 263..264),(SquareL, 264..265),(NumLit, 265..266),(Space, 266..267),(NumLit, 267..268),(Space, 268..269),(NumLit, 269..270),(SquareR, 270..271),(Col, 271..272),(Id, 272..273),
      (Newline, 273..281),(SquareL, 281..282),(NumLit, 282..283),(Space, 283..284),(NumLit, 284..285),(Space, 285..286),(NumLit, 286..287),(SquareR, 287..288),
      (Newline, 288..295),(SquareR, 295..296),(Col, 296..297),(Id, 297..298),
      (Newline, 298..312),(Id, 312..313),(Alias, 313..316),(Id, 316..319),(Col, 319..320),(RoundL, 320..321),(Id, 321..322),(Alias, 322..325),(Id, 325..330),(Col, 330..331),(NumLit, 331..332),(Col, 332..333),(Id, 333..336),(RoundR, 336..337),
      (Newline, 337..344),(SquareL, 344..345),(SquareL, 345..346),(NumLit, 346..347),(Space, 347..348),(NumLit, 348..349),(Space, 349..350),(NumLit, 350..351),(SquareR, 351..352),(Col, 352..353),(Id, 353..354),
      (Newline, 354..362),(SquareL, 362..363),(NumLit, 363..364),(Space, 364..365),(NumLit, 365..366),(Space, 366..367),(NumLit, 367..368),(SquareR, 368..369),
      (Newline, 369..376),(SquareR, 376..377),(Col, 377..378),(Id, 378..379),
      (Newline, 379..393),(Id, 393..394),(Alias, 394..397),(Id, 397..400),(Col, 400..401),(RoundL, 401..402),(Id, 402..405),(Col, 405..406),(Id, 406..409),(RoundR, 409..410),
      (Newline, 410..417),(SquareL, 417..418),(SquareL, 418..419),(Id, 419..422),(SquareR, 422..423),(SquareR, 423..424),(Col, 424..425),(Id, 425..427),
      (Newline, 427..441),(SquareL, 441..442),(Id, 442..445),(SquareR, 445..446),(Col, 446..447),(Id, 447..450),(Col, 450..451),(Id, 451..454),
      (Newline, 454..468),(SquareL, 468..469),(Id, 469..472),(SquareR, 472..473),(Col, 473..474),(Id, 474..479),(Col, 479..480),(NumLit, 480..481),(Col, 481..482),(Id, 482..485),
      (Newline, 485..492),(SquareL, 492..493),(Id, 493..496),(SquareR, 496..497),(Col, 497..498),(Id, 498..501),(Col, 501..502),(Id, 502..505),
      (Newline, 505..512),(SquareL, 512..513),(Id, 513..516),(SquareR, 516..517),(Col, 517..518),(Id, 518..524),
      (Newline, 524..530)
    ];
    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    lex.spanned().zip(expected.into_iter()).for_each(|(input,ex)|assert_eq!(input,ex));    
    // for e in lex.spanned() {println!("{e:?},")};
    // print_tokens(example,lex)
  }

  #[test]fn recursive_functions(){
    let example = r#"

      fib :: <=_1.if_id_(fib.@_dec + fib.@_(dec @ dec))
      fib :: \{<=_1.if_id_(:0.@_dec + :0.@_(dec @ dec))}
      (fib :: ?{         :# a fibonacci function
          b :| <=_1 :: b 
          g         :: g . :?.@_dec + :?.@_(dec @ dec)
        }
      )

    "#;
    use Token::*;
    let expected = [
      (Newline, 0..8),(Id, 8..11),(Space, 11..12),(Def, 12..15),(Id, 15..17),(Underbar, 17..18),(NumLit, 18..19),(Dot, 19..20),(Id, 20..22),(Underbar, 22..23),(Id, 23..25),(Underbar, 25..26),(RoundL, 26..27),(Id, 27..30),(Dot, 30..31),(Id, 31..32),(Underbar, 32..33),(Id, 33..36),(Space, 36..37),(Id, 37..38),(Space, 38..39),(Id, 39..42),(Dot, 42..43),(Id, 43..44),(Underbar, 44..45),(RoundL, 45..46),(Id, 46..49),(Space, 49..50),(Id, 50..51),(Space, 51..52),(Id, 52..55),(RoundR, 55..56),(RoundR, 56..57),
      (Newline, 57..64),(Id, 64..67),(Space, 67..68),(Def, 68..71),(Lambda, 71..73),(Id, 73..75),(Underbar, 75..76),(NumLit, 76..77),(Dot, 77..78),(Id, 78..80),(Underbar, 80..81),(Id, 81..83),(Underbar, 83..84),(RoundL, 84..85),(Col, 85..86),(NumLit, 86..87),(Dot, 87..88),(Id, 88..89),(Underbar, 89..90),(Id, 90..93),(Space, 93..94),(Id, 94..95),(Space, 95..96),(Col, 96..97),(NumLit, 97..98),(Dot, 98..99),(Id, 99..100),(Underbar, 100..101),(RoundL, 101..102),(Id, 102..105),(Space, 105..106),(Id, 106..107),(Space, 107..108),(Id, 108..111),(RoundR, 111..112),(RoundR, 112..113),(CurlyR, 113..114),
      (Newline, 114..121),(RoundL, 121..122),(Id, 122..125),(Space, 125..126),(Def, 126..129),(Match, 129..140),(Col, 140..141),(Id, 141..142),(Space, 142..143),(Id, 143..144),(Space, 144..145),(Id, 145..154),(Space, 154..155),(Id, 155..163),
      (Newline, 163..174),(Id, 174..175),(MatchGuard, 175..179),(Id, 179..181),(Underbar, 181..182),(NumLit, 182..183),(Space, 183..184),(Def, 184..187),(Id, 187..188),
      (Newline, 188..200),(Id, 200..201),(Space, 201..210),(Def, 210..213),(Id, 213..214),(Space, 214..215),(Dot, 215..216),(Space, 216..217),(MatchRec, 217..219),(Dot, 219..220),(Id, 220..221),(Underbar, 221..222),(Id, 222..225),(Space, 225..226),(Id, 226..227),(Space, 227..228),(MatchRec, 228..230),(Dot, 230..231),(Id, 231..232),(Underbar, 232..233),(RoundL, 233..234),(Id, 234..237),(Space, 237..238),(Id, 238..239),(Space, 239..240),(Id, 240..243),(RoundR, 243..244),
      (Newline, 244..253),(CurlyR, 253..254),
      (Newline, 254..261),(RoundR, 261..262),
      (Newline, 262..268)
    ];
    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    lex.spanned().zip(expected.into_iter()).for_each(|(input,ex)|assert_eq!(input,ex));    
    // for e in lex.spanned() {println!("{e:?},")};
    // print_tokens(example,lex)
  }
  #[test]fn fizzbuz(){
    let example = r#"

        (fizzbuzz [(:: num [string])
          f :: "fizz"
          b :: "buzz"
        ]
        iota . (1 +).fmap
        .
        mod_3.fmap zip mod_5.fmap
        .
        ?{
          ,(0 0) :: f cat b
          ,(0 _) :: f
          ,(_ 0) :: b
        }.fmap
      )
      fizzbuzz_70

    "#;
    use Token::*;
    let expected =[
      (Newline, 0..10),(RoundL, 10..11),(Id, 11..19),(Space, 19..20),(SquareL, 20..21),(RoundL, 21..22),(Def, 22..25),(Id, 25..28),(Space, 28..29),(SquareL, 29..30),(Id, 30..36),(SquareR, 36..37),(RoundR, 37..38),  
      (Newline, 38..49),(Id, 49..50),(Space, 50..51),(Def, 51..54),(StrLit, 54..60),
      (Newline, 60..71),(Id, 71..72),(Space, 72..73),(Def, 73..76),(StrLit, 76..82),
      (Newline, 82..91),(SquareR, 91..92),
      (Newline, 92..101),(Id, 101..105),(Space, 105..106),(Dot, 106..107),(Space, 107..108),(RoundL, 108..109),(NumLit, 109..110),(Space, 110..111),(Id, 111..112),(RoundR, 112..113),(Dot, 113..114),(Id, 114..118),
      (Newline, 118..127),(Dot, 127..128),
      (Newline, 128..137),(Id, 137..140),(Underbar, 140..141),(NumLit, 141..142),(Dot, 142..143),(Id, 143..147),(Space, 147..148),(Id, 148..151),(Space, 151..152),(Id, 152..155),(Underbar, 155..156),(NumLit, 156..157),(Dot, 157..158),(Id, 158..162),
      (Newline, 162..171),(Dot, 171..172),
      (Newline, 172..181),(Match, 181..183),
      (Newline, 183..194),(Tuple, 194..196),(NumLit, 196..197),(Space, 197..198),(NumLit, 198..199),(RoundR, 199..200),(Space, 200..201),(Def, 201..204),(Id, 204..205),(Space, 205..206),(Id, 206..209),(Space, 209..210),(Id, 210..211),
      (Newline, 211..222),(Tuple, 222..224),(NumLit, 224..225),(Space, 225..226),(Underbar, 226..227),(RoundR, 227..228),(Space, 228..229),(Def, 229..232),(Id, 232..233),
      (Newline, 233..244),(Tuple, 244..246),(Underbar, 246..247),(Space, 247..248),(NumLit, 248..249),(RoundR, 249..250),(Space, 250..251),(Def, 251..254),(Id, 254..255),
      (Newline, 255..264),(CurlyR, 264..265),(Dot, 265..266),(Id, 266..270),
      (Newline, 270..277),(RoundR, 277..278),
      (Newline, 278..285),(Id, 285..293),(Underbar, 293..294),(NumLit, 294..296),
      (Newline, 296..302)
    ];
    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    // lex.spanned().zip(expected.into_iter()).for_each(|(input,ex)|assert_eq!(input,ex));    
    // for e in lex.spanned() {println!("{e:?},")};
    print_tokens(example,lex)
  }

  #[test]fn unsorted(){
    let example = r#"

      [[1 2] [3 4]] . 1.((+./ % #).rank)   :# f.g.h == h_(g_f)


      (integer_5.?{
        5.i8  :: 1
        5.i16 :: 2
        5.i32 :: 3
        5.i64 :: 4
        a :: 0
      })

      \{:3 {:2} :1}
      ?{,(a b) c (:: ,(num num) num num) 
        b - a + c
      }

      (   config := 1{
        test := {(version := string) (log := bool)}  :# record variant
        (dev := { 
          version := string 
          hash    := u128
        })
        default
        basic
        tagged:(vec:string)
      })

      g : u8
      j := array:2:2{a b}

      f : {a b c}
      k : {d e f}
      u : {f k}    :# <=> {a b c d e f}
      i := 1{u}

    "#;
    use Token::*;
    let expected =[
      (Newline, 0..8),(SquareL, 8..9),(SquareL, 9..10),(NumLit, 10..11),(Space, 11..12),(NumLit, 12..13),(SquareR, 13..14),(Space, 14..15),(SquareL, 15..16),(NumLit, 16..17),(Space, 17..18),(NumLit, 18..19),(SquareR, 19..20),(SquareR, 20..21),(Space, 21..22),(Dot, 22..23),(Space, 23..24),(NumLit, 24..25),(Dot, 25..26),(RoundL, 26..27),(RoundL, 27..28),(Id, 28..29),(Dot, 29..30),(Id, 30..31),(Space, 31..32),(Id, 32..33),(Space, 33..34),(Id, 34..35),(RoundR, 35..36),(Dot, 36..37),(Id, 37..41),(RoundR, 41..42),
      (Newline, 64..73),(RoundL, 73..74),(Id, 74..81),(Underbar, 81..82),(NumLit, 82..83),(Dot, 83..84),(Match, 84..86),
      (Newline, 86..95),(NumLit, 95..96),(Dot, 96..97),(Id, 97..99),(Space, 99..101),(Def, 101..104),(NumLit, 104..105),
      (Newline, 105..114),(NumLit, 114..115),(Dot, 115..116),(Id, 116..119),(Space, 119..120),(Def, 120..123),(NumLit, 123..124),
      (Newline, 124..133),(NumLit, 133..134),(Dot, 134..135),(Id, 135..138),(Space, 138..139),(Def, 139..142),(NumLit, 142..143),
      (Newline, 143..152),(NumLit, 152..153),(Dot, 153..154),(Id, 154..157),(Space, 157..158),(Def, 158..161),(NumLit, 161..162),
      (Newline, 162..171),(Id, 171..172),(Space, 172..173),(Def, 173..176),(NumLit, 176..177),
      (Newline, 177..184),(CurlyR, 184..185),(RoundR, 185..186),
      (Newline, 186..194),(Lambda, 194..196),(Col, 196..197),(NumLit, 197..198),(Space, 198..199),(CurlyL, 199..200),(Col, 200..201),(NumLit, 201..202),(CurlyR, 202..203),(Space, 203..204),(Col, 204..205),(NumLit, 205..206),(CurlyR, 206..207),
      (Newline, 207..214),(Match, 214..216),(Tuple, 216..218),(Id, 218..219),(Space, 219..220),(Id, 220..221),(RoundR, 221..222),(Space, 222..223),(Id, 223..224),(Space, 224..225),(RoundL, 225..226),(Def, 226..229),(Tuple, 229..231),(Id, 231..234),(Space, 234..235),(Id, 235..238),(RoundR, 238..239),(Space, 239..240),(Id, 240..243),(Space, 243..244),(Id, 244..247),(RoundR, 247..248),
      (Newline, 248..258),(Id, 258..259),(Space, 259..260),(Id, 260..261),(Space, 261..262),(Id, 262..263),(Space, 263..264),(Id, 264..265),(Space, 265..266),(Id, 266..267),
      (Newline, 267..274),(CurlyR, 274..275),
      (Newline, 275..283),(RoundL, 283..287),(Id, 287..293),(Newtype, 293..297),(Elements, 297..299),
      (Newline, 299..308),(Id, 308..312),(Newtype, 312..316),(CurlyL, 316..317),(RoundL, 317..318),(Id, 318..325),(Newtype, 325..329),(Id, 329..335),(RoundR, 335..336),(Space, 336..337),(RoundL, 337..338),(Id, 338..341),(Newtype, 341..345),(Id, 345..349),(RoundR, 349..350),(CurlyR, 350..351),
      (Newline, 370..379),(RoundL, 379..380),(Id, 380..383),(Newtype, 383..387),(CurlyL, 387..389),
      (Newline, 389..400),(Id, 400..407),(Newtype, 407..411),(Id, 411..417),
      (Newline, 417..429),(Id, 429..433),(Newtype, 433..440),(Id, 440..444),
      (Newline, 444..453),(CurlyR, 453..454),(RoundR, 454..455),
      (Newline, 455..464),(Id, 464..471),
      (Newline, 471..480),(Id, 480..485),
      (Newline, 485..494),(Id, 494..500),(Col, 500..501),(RoundL, 501..502),(Id, 502..505),(Col, 505..506),(Id, 506..512),(RoundR, 512..513),
      (Newline, 513..520),(CurlyR, 520..521),(RoundR, 521..522),
      (Newline, 522..530),(Id, 530..531),(Alias, 531..534),(Id, 534..536),
      (Newline, 536..543),(Id, 543..544),(Newtype, 544..548),(Id, 548..553),(Col, 553..554),(NumLit, 554..557),(CurlyL, 557..558),(Id, 558..559),(Space, 559..560),(Id, 560..561),(CurlyR, 561..562),
      (Newline, 562..570),(Id, 570..571),(Alias, 571..574),(CurlyL, 574..575),(Id, 575..576),(Space, 576..577),(Id, 577..578),(Space, 578..579),(Id, 579..580),(CurlyR, 580..581),
      (Newline, 581..588),(Id, 588..589),(Alias, 589..592),(CurlyL, 592..593),(Id, 593..594),(Space, 594..595),(Id, 595..596),(Space, 596..597),(Id, 597..598),(CurlyR, 598..599),
      (Newline, 599..606),(Id, 606..607),(Alias, 607..610),(CurlyL, 610..611),(Id, 611..612),(Space, 612..613),(Id, 613..614),(CurlyR, 614..615),
      (Newline, 639..646),(Id, 646..647),(Newtype, 647..651),(Elements, 651..653),(Id, 653..654),(CurlyR, 654..655),
      (Newline, 655..661),
    ];
    let lex : logos::Lexer<'_, Token> = Token::lexer(example);
    lex.spanned().zip(expected.into_iter()).for_each(|(input,ex)|assert_eq!(input,ex));    
    // for e in lex.spanned() {println!("{e:?},")};
    // print_tokens(example,lex)
  }
}

#[allow(unused)]
pub(crate) fn print_tokens<'a>(src: &str ,lex: logos::Lexer<'a, Token>) {
    use concat as cat;
    macro_rules! m {($name:ident $body:tt) => {macro_rules! $name $body};}
    m! {red     {($s:literal) => {cat!{"\u{001b}[31m"      , $s, "\u{001b}[0m"}};}}
    m! {blue    {($s:literal) => {cat!{"\u{001b}[36m"      , $s, "\u{001b}[0m"}};}}
    m! {magenta {($s:literal) => {cat!{"\u{001b}[35m"      , $s, "\u{001b}[0m"}};}}
    m! {grey    {($s:literal) => {cat!{"\u{001b}[38;5;232m", $s, "\u{001b}[0m"}};}}
    m! {yellow  {($s:literal) => {cat!{"\u{001b}[33;1m"    , $s, "\u{001b}[0m"}};}}
    m! {lgrey   {($s:literal) => {cat!{"\u{001b}[38;5;245m", $s, "\u{001b}[0m"}};}}
    m! {pcat    {($($body:expr),+) => {print!(cat!($($body,)+))};}}
    m! {brace   {($c:ident $mid:literal) => {pcat!(grey!("\n    <"), $c!( $mid ), grey!("> "))};}}

    println!();
    for (t,s) in lex.spanned() {
      use Token::*;
      match t {
        Space => print!(grey!("\n  <\" \"> ")),
        Newline =>{
          print!(grey!("\n<\\n>\n"))
        }
        Tuple     => brace!(red ",("),
        RoundL    => brace!(red  "("),
        RoundR    => brace!(red  ")"),
        SquareL   => brace!(blue "["),
        SquareR   => brace!(blue "]"),
        Match     => brace!(magenta "?{{"),
        Lambda    => brace!(magenta "\\{{"),
        CurlyL    => brace!(magenta "{{"),
        CurlyR    => brace!(magenta "}}"),
        Error     => panic!("{:?}", t),
        Elements  => {print!(
          cat!(grey!("\n    <"),magenta!("{}"), grey!("> ")),&src[s]
        )}
        _ => {print!(
          cat!(grey!("<"),yellow!("{}"),"|",lgrey!("{:?}"), grey!("> ")),&src[s],t
        )}
      }
    }
}


/// by the time the TokenTree is done, the newline and space tokens should omitted and
/// replaced with groups
enum TokenTree {
  Def,            // ::
  Col,            // :
  Dot(XFix),      // .
  Underbar(XFix), // _
  Tick(XFix),     // `
  MatchRec,       // :?
  MatchGuard,     // :|
  StrLit{span: core::ops::Range<usize>},
  NumLit{span: core::ops::Range<usize>},
  Id{span: core::ops::Range<usize>},
  LamdaArg(u16)
}

enum XFix{Pre, In, Suf}
enum Brace{
  Curly,  //  {}
  Match,  // ?{}
  Record, // ,{}
  Round,  //  ()
  Tuple,  // ,()
  Square, //  []
}
