import scala.util.parsing.combinator._


object FWSParser extends JavaTokenParsers {

  def variable : Parser[String] = ident
  def valueLabel :Parser[String] = ident
  def typeLabel : Parser[String] = ident

  def expr : Parser[Any] = (
    "val" ~> ((variable <~ "=") <~ "new") ~ (typ <~ ";") ~ expr
    | exprChain
  )

  def exprChain : Parser[Any] =
    variable ~ rep("." ~> valueLabel ~ opt(args))

  def args : Parser[Any] =
    "(" ~ opt(rep1sep(expr, ",")) <~ ")"

  def params : Parser[Any] =
    "(" ~ opt(rep1sep(expr <~ ":" ~ typ, ",")) <~ ")"

  def typ : Parser[Any] = (
    singletonType | typeSignature | typeLabel
  )

  def singletonType : Parser[Any] =
    path <~ ".type"

  def typeSignature : Parser[Any] =
    "(" ~> rep1sep(typ, ",") <~ ")" <~ "{" ~ variable <~ "|" ~ rep(decl) <~ "}"

  def decl : Parser[Any] = (
    "val" ~> valueLabel <~ ":" ~ typ ~ opt("=" ~> expr)
    | "def" ~> valueLabel <~ params <~ ":" ~ typ ~ opt("=" ~> expr)
    | "type" ~> typeLabel ~ opt("=" ~> typ)
    | "trait" ~> typeLabel ~ typeSignature
  )

  def path : Parser[Any] =
    variable <~ rep("." ~> valueLabel)

}
