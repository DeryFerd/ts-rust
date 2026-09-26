//! Source member names retain the row selected at publication. A later named
//! value does not change an original row into a proxy or replace a proxy.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
struct PropertyNameRow {
    symbol: SemanticSymbolId,
    name: EscapedName,
    flags: SymbolFlags,
    checks: CheckFlags,
    declarations: Option<Vec<NodeRef>>,
    value_declaration: Option<NodeRef>,
    parent: Option<SemanticSymbolId>,
    links: ValueSymbolLinks,
    source_readonly: Option<bool>,
}

impl PropertyNameRow {
    fn read(store: &CanonicalTypeMapperStore, symbol: SemanticSymbolId, source_readonly: Option<bool>) -> Result<Self, RelationUnavailable> {
        let invalid = || RelationUnavailable::InvalidSymbolMembers(symbol);
        let record = store.symbol(symbol).ok_or_else(invalid)?;
        let mut links = store.value_symbol_links(symbol).cloned().unwrap_or_default();
        if store.get_merged_symbol(symbol) != Some(symbol)
            || record.members().is_some() || record.exports().is_some()
            || record.export_symbol().is_some()
            || links.resolved_type.is_some_and(|type_| store.type_payload(type_).is_none())
        {
            return Err(invalid());
        }
        // Only the named value is outside this receipt. Target, mapper, and
        // all other link fields remain part of the exact row identity.
        links.resolved_type = None;
        let checks = if let Some(readonly) = source_readonly {
            let expected = if readonly { CheckFlags::READONLY } else { CheckFlags::NONE };
            if record.check_flags() != CheckFlags::NONE && record.check_flags() != expected {
                return Err(invalid());
            }
            // Publishing a declared value installs this source-derived bit.
            // Names use the declaration before and after that publication.
            expected
        } else {
            record.check_flags()
        };
        Ok(Self {
            symbol, name: record.name().to_owned(), flags: record.flags(), checks,
            declarations: record.declarations().map(<[NodeRef]>::to_vec),
            value_declaration: record.value_declaration(), parent: record.parent(), links, source_readonly,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::semantic) struct SourcePropertyObjectMemberNames {
    projection: SourcePropertyObjectProjection,
    members: PropertyObjectAliasMembers,
    source_members: Option<SymbolTableId>,
    source_rows: Vec<PropertyNameRow>,
    rows: Vec<PropertyNameRow>,
}

impl SourcePropertyObjectMemberNames {
    pub(in crate::semantic) fn members(&self) -> &PropertyObjectAliasMembers {
        &self.members
    }

    pub(in crate::semantic) fn source_properties(&self) -> &[crate::semantic::object_members::PlannedProperty] {
        self.projection.properties()
    }

    pub(in crate::semantic) fn validate(
        &self,
        store: &CanonicalTypeMapperStore,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<(), RelationUnavailable> {
        let receiver = self.members.receiver;
        let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
        if source_property_object_projection(store, receiver)?.as_ref() != Some(&self.projection) {
            return Err(invalid());
        }
        if store.symbol(self.projection.source_symbol()).ok_or_else(invalid)?.members() != self.source_members {
            return Err(invalid());
        }
        validate_source_property_object_cache_cycles_with_replay(
            store, &self.projection, array_targets, false,
        )?;
        for (type_, expected_members, expected_properties) in [
            (self.projection.target(), self.source_members, self.source_rows.iter().map(|row| row.symbol).collect::<Vec<_>>()),
            (receiver, self.members.members, self.members.properties.clone()),
        ] {
            let record = store.type_payload(type_).ok_or_else(invalid)?;
            if !record.object_flags().contains(ObjectFlags::MEMBERS_RESOLVED) {
                return Err(invalid());
            }
            let (members, properties) = property_object_alias_member_table(store, type_, expected_properties.len())?;
            if members != expected_members || properties != expected_properties {
                return Err(invalid());
            }
            for symbol in properties {
                let row = store.symbol(*symbol).ok_or_else(invalid)?;
                if members.and_then(|table| store.symbol_table(table))
                    .and_then(|table| table.get(row.name())) != Some(*symbol)
                {
                    return Err(invalid());
                }
            }
        }
        for expected in self.source_rows.iter().chain(&self.rows) {
            if PropertyNameRow::read(store, expected.symbol, expected.source_readonly)? != *expected {
                return Err(invalid());
            }
        }
        Ok(())
    }
}

pub(in crate::semantic) fn capture_source_property_object_member_names(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourcePropertyObjectMemberNames, RelationUnavailable> {
    let projection = source_property_object_projection(store, receiver)?
        .ok_or(RelationUnavailable::UnsupportedStructuredType(receiver))?;
    let members = validate_property_object_alias_members_with_array_targets(store, receiver, array_targets)?
        .ok_or(RelationUnavailable::UnresolvedStructuredMembers(receiver))?;
    let proof = SourcePropertyObjectMemberNames {
        source_members: store.symbol(projection.source_symbol())
            .ok_or(RelationUnavailable::InvalidStructuredMembers(receiver))?.members(),
        source_rows: projection.properties().iter().map(|property| PropertyNameRow::read(store, property.symbol, Some(property.readonly)))
            .collect::<Result<Vec<_>, _>>()?,
        rows: members.properties.iter().zip(projection.properties()).map(|(symbol, source)| {
            PropertyNameRow::read(store, *symbol, (*symbol == source.symbol).then_some(source.readonly))
        })
            .collect::<Result<Vec<_>, _>>()?,
        projection, members,
    };
    proof.validate(store, array_targets)?;
    Ok(proof)
}
