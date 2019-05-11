import scala.util.parsing.combinator._


sealed trait Ast
case class ValNewIn(x : String, ty : Type, e : Ast)   extends Ast
case class Var(x : String)                            extends Ast
case class Access(e : Ast, vl : String)               extends Ast
case class Call(e : Ast, vl : String, es : List[Ast]) extends Ast


case class Path(x : String, vls : List[String])


case class Intersection[A](tys : List[A], x : String, decls : List[Declaration])


sealed trait Type
case class TypeSelection(p : Path, tl : String)      extends Type
case class SingletonType(p : Path)                   extends Type
case class TypeSignature(tysig : Intersection[Type]) extends Type


sealed trait Value
case class ValVar(x : String) extends Value
  /* --
     All the values (i.e. objects) are stored in the evaluation environment,
     and thus we can handle every value in the form of a variable name.
     -- */


sealed trait TypeValue
case class ValTypeSelection(x : String, tl : String)         extends TypeValue
case class ValSingletonType(p : Path)                        extends TypeValue
case class ValTypeSignature(tysig : Intersection[TypeValue]) extends TypeValue


sealed trait ValueDeclBody
case class DeclVal(ty : Type, eopt : Option[Ast])                                   extends ValueDeclBody
case class DeclDef(params : List[(String, Type)], tyans : Type, eopt : Option[Ast]) extends ValueDeclBody


sealed trait TypeDeclBody
case class DeclType(tyopt : Option[Type])        extends TypeDeclBody
case class DeclTrait(tysig : Intersection[Type]) extends TypeDeclBody


sealed trait Declaration
case class DeclForValueLabel(vl : String, vd : ValueDeclBody) extends Declaration
case class DeclForTypeLabel(tl : String, td : TypeDeclBody)   extends Declaration


object FWSParser extends JavaTokenParsers {

  val reservedWord = List("val", "def", "new", "type", "trait")

  def variable : Parser[String] =
    ident ^? {
      case s if (!(reservedWord.contains(s))) => s
    }

  def valueLabel : Parser[String] =
    ident ^? {
      case s if (!(reservedWord.contains(s)) && s.head.isLower) => s
    }

  def typeLabel : Parser[String] =
    ident ^? {
      case s if (!(reservedWord.contains(s)) && s.head.isUpper) => s
    }

  def expr : Parser[Ast] =
    ( "val" ~> ((variable <~ "=") <~ "new") ~ (typ <~ ";") ~ expr ^^ {
        case x ~ ty ~ e => ValNewIn(x, ty, e)
      }
    | exprChain
    )

  def exprChain : Parser[Ast] =
    variable ~ rep("." ~> valueLabel ~ opt(args)) ^^ {
      case x ~ lst =>
        val init : Ast = Var(x);
        lst.foldLeft(init)((eacc, pair) =>
          pair match {
            case vl ~ None     => Access(eacc, vl)
            case vl ~ Some(es) => Call(eacc, vl, es)
          }
        )
    }

  def args : Parser[List[Ast]] =
    "(" ~> (opt(rep1sep(expr, ",")) <~ ")") ^^ {
      case None     => Nil
      case Some(es) => es
    }

  def params : Parser[List[(String, Type)]] =
    "(" ~> (opt(rep1sep((variable <~ ":") ~ typ, ",")) <~ ")") ^^ {
      case None      => Nil
      case Some(lst) => lst.map({ case e ~ ty => (e, ty)})
    }

  def typ : Parser[Type] =
    ( singletonType
    | typeSignature ^^ {
        case tysig => TypeSignature(tysig)
      }
    | (path <~ ".") ~ typeLabel ^^ {
        case p ~ tl => TypeSelection(p, tl)
      }
    )

  def singletonType : Parser[Type] =
    path <~ ".type" ^^ {
      case p => SingletonType(p)
    }

  def typeSignature : Parser[Intersection[Type]] =
    "(" ~> ((rep1sep(typ, ",") <~ ")") <~ "{") ~ (variable <~ "|") ~ (rep(decl) <~ "}") ^^ {
      case tys ~ x ~ decls => Intersection(tys, x, decls)
    }

  def decl : Parser[Declaration] =
    ( "val" ~> (valueLabel <~ ":") ~ typ ~ opt("=" ~> expr) ^^ {
        case vl ~ ty ~ eopt => DeclForValueLabel(vl, DeclVal(ty, eopt))
      }
    | "def" ~> valueLabel ~ (params <~ ":") ~ typ ~ opt("=" ~> expr) ^^ {
        case vl ~ pars ~ ty ~ eopt => DeclForValueLabel(vl, DeclDef(pars, ty, eopt))
      }
    | "type" ~> typeLabel ~ opt("=" ~> typ) ^^ {
        case tl ~ tyopt => DeclForTypeLabel(tl, DeclType(tyopt))
      }
    | "trait" ~> typeLabel ~ typeSignature ^^ {
        case tl ~ tysig => DeclForTypeLabel(tl, DeclTrait(tysig))
      }
    )

  def path : Parser[Path] =
    variable ~ rep("." ~> valueLabel) ^^ {
      case x ~ vls => Path(x, vls)
    }

}
