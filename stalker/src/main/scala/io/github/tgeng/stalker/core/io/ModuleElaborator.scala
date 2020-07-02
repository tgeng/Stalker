package io.github.tgeng.stalker.core.io

import scala.collection.mutable
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.common.extraSetOps
import io.github.tgeng.stalker
import stalker.common._
import stalker.core.tt._
import Error._
import QualifiedName._
import PreDeclaration._

class ModuleElaborator(val mutualGroupLoader: MutualGroupLoader) {

  private val cache = mutable.Map[MutualGroup, Result[Set[Declaration]]]()

  def elaborate(mutualGroup: MutualGroup): Result[Set[Declaration]] = {
    elaborateImpl(mutualGroup, SignatureBuilder.create())
  }

  def elaborateImpl(mutualGroup: MutualGroup, sig: SignatureBuilder): Result[Set[Declaration]] = cache.getOrElseUpdate(mutualGroup, {
    for {
      depMutualGroups <- mutualGroup.deps.liftMap { qn => mutualGroupLoader.loadContainingMutualGroup(qn) }
      _ = (depMutualGroups | mutualGroup.depMutualGroups).foreach {
        // TODO(tgeng): read and write to disk cache
        elaborateImpl(_, sig)
      }

      // First add all type declarations to the signature
      decls : Set[Set[Declaration]] <- mutualGroup.declarations.liftMap {
        case d: PreData => for (data, definition) <- sig.elaborateDataType(d)
                           yield {
                             sig += data
                             sig += definition
                             Set(definition)
                           }
        case r: PreRecord => for (record, definition) <- sig.elaborateRecordType(r)
                             yield {
                               sig += record
                               sig += definition
                               Set(definition)
                             }
        case d: PreDefinition => for definition <- sig.elaborateDefinitionType(d)
                                 yield {
                                   sig += definition
                                   Set()
                                 }
      }
      // Next add all body definitions
      moreDecls : Set[Set[Declaration]] <- mutualGroup.declarations.liftMap {
        case d: PreData => for data <- sig.elaborateDataConstructors(d)
                           yield {
                             sig += data
                             Set(data)
                           }
        case r: PreRecord => for record <- sig.elaborateRecordFields(r)
                             yield {
                               sig += record
                               Set(record)
                             }
        case d: PreDefinition => for definition <- sig.elaborateDefinitionClauses(d)
                                 yield {
                                   sig += definition
                                   Set(definition)
                                 }
      }
    } yield (decls | moreDecls).flatten
  })
}