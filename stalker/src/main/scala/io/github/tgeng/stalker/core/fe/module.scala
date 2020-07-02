package io.github.tgeng.stalker.core.fe

enum Visibility extends Serializable {
  case Public, Internal, Private
}

enum ModuleCommand {
  case MNsOp(src: List[String], dstNames: List[String], dstScope: Visibility)
  case MDecl(decl: FDeclaration, visibility: Visibility)
}

case class Module(
  commands: Seq[ModuleCommand]
)