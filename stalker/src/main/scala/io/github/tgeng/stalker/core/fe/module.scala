package io.github.tgeng.stalker.core.fe

enum ModuleCommand {
  case MImport(src: List[String], dst: List[String], shouldExport: Boolean)
  case MExport(src: List[String], dst: List[String])
  case MDecl(decl: FDeclaration, shouldExport: Boolean)
}
