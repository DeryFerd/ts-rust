//! Constant evaluation over the generated TypeScript AST.

use std::collections::BTreeMap;

use ts_ast::{NodeArena, NodeData, NodeId, SyntaxKind};
use ts_jsnum::{Number, PseudoBigInt};

/// A value produced by constant evaluation.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Number(Number),
    String(String),
    Boolean(bool),
    BigInt(PseudoBigInt),
    Null,
    Undefined,
    Array(Vec<Self>),
    Object(BTreeMap<String, Self>),
}

impl Value {
    #[must_use]
    pub fn is_truthy(&self) -> bool {
        match self {
            Self::String(value) => !value.is_empty(),
            Self::Number(value) => value.0 != 0.0 && !value.is_nan(),
            Self::Boolean(value) => *value,
            Self::BigInt(value) => value.sign() != 0,
            Self::Null | Self::Undefined => false,
            Self::Array(_) | Self::Object(_) => true,
        }
    }

    #[must_use]
    pub fn js_string(&self) -> String {
        match self {
            Self::Number(value) => value.to_string(),
            Self::String(value) => value.clone(),
            Self::Boolean(value) => value.to_string(),
            Self::BigInt(value) => value.to_string(),
            Self::Null => "null".to_owned(),
            Self::Undefined => "undefined".to_owned(),
            Self::Array(values) => values
                .iter()
                .map(|value| match value {
                    Self::Null | Self::Undefined => String::new(),
                    _ => value.js_string(),
                })
                .collect::<Vec<_>>()
                .join(","),
            Self::Object(_) => "[object Object]".to_owned(),
        }
    }
}

/// Metadata retained while evaluating expressions.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct EvaluationMetadata {
    pub is_syntactically_string: bool,
    pub resolved_other_files: bool,
    pub has_external_references: bool,
}

impl EvaluationMetadata {
    fn merge(self, other: Self) -> Self {
        Self {
            is_syntactically_string: self.is_syntactically_string || other.is_syntactically_string,
            resolved_other_files: self.resolved_other_files || other.resolved_other_files,
            has_external_references: self.has_external_references || other.has_external_references,
        }
    }
}

/// Why an expression could not be reduced to a constant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnknownReason {
    UnresolvedEntity(NodeId),
    UnsupportedSyntax(SyntaxKind),
    UnsupportedOperator(SyntaxKind),
    InvalidOperands(SyntaxKind),
}

/// A structurally invalid AST or malformed literal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvaluationError {
    MissingNode(NodeId),
    MalformedNode { node: NodeId, kind: SyntaxKind },
    InvalidNumericLiteral { node: NodeId, text: String },
    InvalidBigIntLiteral { node: NodeId, text: String },
}

/// Explicit constant, unknown, or error result.
#[derive(Clone, Debug, PartialEq)]
pub enum EvaluationOutcome {
    Value(Value),
    Unknown(UnknownReason),
    Error(EvaluationError),
}

/// One evaluation result and its upstream-compatible metadata.
#[derive(Clone, Debug, PartialEq)]
pub struct Evaluation {
    pub outcome: EvaluationOutcome,
    pub metadata: EvaluationMetadata,
}

impl Evaluation {
    #[must_use]
    pub const fn known(value: Value) -> Self {
        Self {
            outcome: EvaluationOutcome::Value(value),
            metadata: EvaluationMetadata {
                is_syntactically_string: false,
                resolved_other_files: false,
                has_external_references: false,
            },
        }
    }

    #[must_use]
    pub const fn unknown(reason: UnknownReason) -> Self {
        Self {
            outcome: EvaluationOutcome::Unknown(reason),
            metadata: EvaluationMetadata {
                is_syntactically_string: false,
                resolved_other_files: false,
                has_external_references: false,
            },
        }
    }

    #[must_use]
    pub const fn error(error: EvaluationError) -> Self {
        Self {
            outcome: EvaluationOutcome::Error(error),
            metadata: EvaluationMetadata {
                is_syntactically_string: false,
                resolved_other_files: false,
                has_external_references: false,
            },
        }
    }

    #[must_use]
    pub fn value(&self) -> Option<&Value> {
        if let EvaluationOutcome::Value(value) = &self.outcome {
            Some(value)
        } else {
            None
        }
    }
}

/// Evaluates an expression without external entity resolution.
#[must_use]
pub fn evaluate(arena: &NodeArena, expression: NodeId) -> Evaluation {
    evaluate_with(arena, expression, &mut |node| {
        Evaluation::unknown(UnknownReason::UnresolvedEntity(node))
    })
}

/// Evaluates an expression, delegating identifiers and unresolved entity-name
/// property accesses to `resolve_entity`.
#[must_use]
pub fn evaluate_with(
    arena: &NodeArena,
    expression: NodeId,
    resolve_entity: &mut impl FnMut(NodeId) -> Evaluation,
) -> Evaluation {
    Evaluator {
        arena,
        resolve_entity,
    }
    .evaluate(expression)
}

struct Evaluator<'a, F> {
    arena: &'a NodeArena,
    resolve_entity: &'a mut F,
}

impl<F: FnMut(NodeId) -> Evaluation> Evaluator<'_, F> {
    #[allow(clippy::too_many_lines)]
    fn evaluate(&mut self, id: NodeId) -> Evaluation {
        let Some(node) = self.arena.get(id).cloned() else {
            return Evaluation::error(EvaluationError::MissingNode(id));
        };
        match &node.data {
            NodeData::ParenthesizedExpression(data) => self.evaluate(data.expression),
            NodeData::AsExpression(data) => self.evaluate(data.expression),
            NodeData::NonNullExpression(data) => self.evaluate(data.expression),
            NodeData::SatisfiesExpression(data) => self.evaluate(data.expression),
            NodeData::TypeAssertion(data) => self.evaluate(data.expression),
            NodeData::NumericLiteral(data) => Self::evaluate_number(id, &data.text),
            NodeData::BigIntLiteral(data) => Self::evaluate_bigint(id, &data.text),
            NodeData::StringLiteral(data) => string_evaluation(&data.text),
            NodeData::NoSubstitutionTemplateLiteral(data) => string_evaluation(&data.text),
            NodeData::KeywordExpression(_) => match node.kind {
                SyntaxKind::TrueKeyword => Evaluation::known(Value::Boolean(true)),
                SyntaxKind::FalseKeyword => Evaluation::known(Value::Boolean(false)),
                SyntaxKind::NullKeyword => Evaluation::known(Value::Null),
                _ => Evaluation::unknown(UnknownReason::UnsupportedSyntax(node.kind)),
            },
            NodeData::Identifier(_) => (self.resolve_entity)(id),
            NodeData::PrefixUnaryExpression(data) => {
                self.evaluate_prefix(data.operator, data.operand)
            }
            NodeData::BinaryExpression(data) => {
                let Some(operator) = self.arena.get(data.operator_token).map(|node| node.kind)
                else {
                    return Evaluation::error(EvaluationError::MissingNode(data.operator_token));
                };
                self.evaluate_binary(operator, data.left, data.right)
            }
            NodeData::ConditionalExpression(data) => {
                self.evaluate_conditional(data.condition, data.when_true, data.when_false)
            }
            NodeData::TemplateExpression(data) => {
                self.evaluate_template(data.head, &data.template_spans.nodes)
            }
            NodeData::ArrayLiteralExpression(data) => self.evaluate_array(&data.elements.nodes),
            NodeData::ObjectLiteralExpression(data) => self.evaluate_object(&data.properties.nodes),
            NodeData::PropertyAccessExpression(data) => self.evaluate_property(
                id,
                data.expression,
                Property::Node(data.name),
                data.question_dot_token.is_some(),
            ),
            NodeData::ElementAccessExpression(data) => self.evaluate_property(
                id,
                data.expression,
                Property::Expression(data.argument_expression),
                data.question_dot_token.is_some(),
            ),
            _ => Evaluation::unknown(UnknownReason::UnsupportedSyntax(node.kind)),
        }
    }

    fn evaluate_number(id: NodeId, text: &str) -> Evaluation {
        let normalized = text.replace('_', "");
        let value = Number::from_string(&normalized);
        if value.is_nan() {
            Evaluation::error(EvaluationError::InvalidNumericLiteral {
                node: id,
                text: text.to_owned(),
            })
        } else {
            Evaluation::known(Value::Number(value))
        }
    }

    fn evaluate_bigint(id: NodeId, text: &str) -> Evaluation {
        let Some(normalized) = normalize_bigint_literal(text) else {
            return Evaluation::error(EvaluationError::InvalidBigIntLiteral {
                node: id,
                text: text.to_owned(),
            });
        };
        Evaluation::known(Value::BigInt(PseudoBigInt::parse_valid(&normalized)))
    }

    fn evaluate_prefix(&mut self, operator: SyntaxKind, operand: NodeId) -> Evaluation {
        let mut result = self.evaluate(operand);
        result.metadata.is_syntactically_string = false;
        let metadata = result.metadata;
        let EvaluationOutcome::Value(value) = result.outcome else {
            return result;
        };
        let outcome = match (operator, value) {
            (SyntaxKind::PlusToken, Value::Number(value)) => Value::Number(value),
            (SyntaxKind::MinusToken, Value::Number(value)) => Value::Number(-value),
            (SyntaxKind::TildeToken, Value::Number(value)) => Value::Number(value.bitwise_not()),
            (SyntaxKind::ExclamationToken, value) => Value::Boolean(!value.is_truthy()),
            _ => {
                return Evaluation {
                    outcome: EvaluationOutcome::Unknown(UnknownReason::InvalidOperands(operator)),
                    metadata,
                };
            }
        };
        Evaluation {
            outcome: EvaluationOutcome::Value(outcome),
            metadata,
        }
    }

    fn evaluate_conditional(
        &mut self,
        condition: NodeId,
        when_true: NodeId,
        when_false: NodeId,
    ) -> Evaluation {
        let condition = self.evaluate(condition);
        let metadata = condition.metadata;
        let EvaluationOutcome::Value(value) = condition.outcome else {
            return condition;
        };
        let mut branch = self.evaluate(if value.is_truthy() {
            when_true
        } else {
            when_false
        });
        branch.metadata = metadata.merge(branch.metadata);
        branch
    }

    fn evaluate_binary(&mut self, operator: SyntaxKind, left: NodeId, right: NodeId) -> Evaluation {
        let left = self.evaluate(left);
        if matches!(left.outcome, EvaluationOutcome::Error(_)) {
            return left;
        }
        let logical = matches!(
            operator,
            SyntaxKind::AmpersandAmpersandToken
                | SyntaxKind::BarBarToken
                | SyntaxKind::QuestionQuestionToken
        );
        if logical {
            let EvaluationOutcome::Value(left_value) = &left.outcome else {
                return left;
            };
            if operator == SyntaxKind::AmpersandAmpersandToken && !left_value.is_truthy()
                || operator == SyntaxKind::BarBarToken && left_value.is_truthy()
                || operator == SyntaxKind::QuestionQuestionToken
                    && !matches!(left_value, Value::Null | Value::Undefined)
            {
                return left;
            }
        }
        let right = self.evaluate(right);
        let metadata = EvaluationMetadata {
            is_syntactically_string: operator == SyntaxKind::PlusToken
                && (left.metadata.is_syntactically_string
                    || right.metadata.is_syntactically_string),
            ..left.metadata.merge(right.metadata)
        };
        let EvaluationOutcome::Value(left_value) = &left.outcome else {
            return Evaluation {
                outcome: left.outcome,
                metadata,
            };
        };
        let EvaluationOutcome::Value(right_value) = &right.outcome else {
            return Evaluation {
                outcome: right.outcome,
                metadata,
            };
        };
        if logical {
            return Evaluation {
                outcome: EvaluationOutcome::Value(right_value.clone()),
                metadata,
            };
        }
        let outcome = binary_value(operator, left_value, right_value).map_or_else(
            || EvaluationOutcome::Unknown(UnknownReason::InvalidOperands(operator)),
            EvaluationOutcome::Value,
        );
        Evaluation { outcome, metadata }
    }

    fn evaluate_template(&mut self, head: NodeId, spans: &[NodeId]) -> Evaluation {
        let Some(head_node) = self.arena.get(head) else {
            return Evaluation::error(EvaluationError::MissingNode(head));
        };
        let NodeData::TemplateHead(head) = &head_node.data else {
            return Evaluation::error(EvaluationError::MalformedNode {
                node: head,
                kind: head_node.kind,
            });
        };
        let mut output = head.text.clone();
        let mut metadata = EvaluationMetadata::default();
        for span_id in spans {
            let Some(span_node) = self.arena.get(*span_id).cloned() else {
                return Evaluation::error(EvaluationError::MissingNode(*span_id));
            };
            let NodeData::TemplateSpan(span) = &span_node.data else {
                return Evaluation::error(EvaluationError::MalformedNode {
                    node: *span_id,
                    kind: span_node.kind,
                });
            };
            let result = self.evaluate(span.expression);
            metadata = metadata.merge(result.metadata);
            let EvaluationOutcome::Value(value) = result.outcome else {
                return Evaluation {
                    outcome: result.outcome,
                    metadata: EvaluationMetadata {
                        is_syntactically_string: true,
                        ..EvaluationMetadata::default()
                    },
                };
            };
            output.push_str(&value.js_string());
            let Some(literal) = self.arena.get(span.literal) else {
                return Evaluation::error(EvaluationError::MissingNode(span.literal));
            };
            match &literal.data {
                NodeData::TemplateMiddle(data) => output.push_str(&data.text),
                NodeData::TemplateTail(data) => output.push_str(&data.text),
                _ => {
                    return Evaluation::error(EvaluationError::MalformedNode {
                        node: span.literal,
                        kind: literal.kind,
                    });
                }
            }
        }
        Evaluation {
            outcome: EvaluationOutcome::Value(Value::String(output)),
            metadata: EvaluationMetadata {
                is_syntactically_string: true,
                ..metadata
            },
        }
    }

    fn evaluate_array(&mut self, elements: &[NodeId]) -> Evaluation {
        let mut values = Vec::with_capacity(elements.len());
        let mut metadata = EvaluationMetadata::default();
        for element in elements {
            let result = self.evaluate(*element);
            metadata = metadata.merge(result.metadata);
            let EvaluationOutcome::Value(value) = result.outcome else {
                return Evaluation {
                    outcome: result.outcome,
                    metadata,
                };
            };
            values.push(value);
        }
        Evaluation {
            outcome: EvaluationOutcome::Value(Value::Array(values)),
            metadata,
        }
    }

    fn evaluate_object(&mut self, properties: &[NodeId]) -> Evaluation {
        let mut values = BTreeMap::new();
        let mut metadata = EvaluationMetadata::default();
        for property_id in properties {
            let Some(node) = self.arena.get(*property_id).cloned() else {
                return Evaluation::error(EvaluationError::MissingNode(*property_id));
            };
            match &node.data {
                NodeData::PropertyAssignment(property) => {
                    let Some(name) = self.property_node_name(property.name) else {
                        return Evaluation::unknown(UnknownReason::UnsupportedSyntax(node.kind));
                    };
                    let result = self.evaluate(property.initializer);
                    metadata = metadata.merge(result.metadata);
                    let EvaluationOutcome::Value(value) = result.outcome else {
                        return Evaluation {
                            outcome: result.outcome,
                            metadata,
                        };
                    };
                    values.insert(name, value);
                }
                NodeData::ShorthandPropertyAssignment(property) => {
                    let Some(name) = self.property_node_name(property.name) else {
                        return Evaluation::unknown(UnknownReason::UnsupportedSyntax(node.kind));
                    };
                    let result = (self.resolve_entity)(property.name);
                    metadata = metadata.merge(result.metadata);
                    let EvaluationOutcome::Value(value) = result.outcome else {
                        return Evaluation {
                            outcome: result.outcome,
                            metadata,
                        };
                    };
                    values.insert(name, value);
                }
                NodeData::SpreadAssignment(spread) => {
                    let result = self.evaluate(spread.expression);
                    metadata = metadata.merge(result.metadata);
                    let EvaluationOutcome::Value(Value::Object(spread_values)) = result.outcome
                    else {
                        return Evaluation::unknown(UnknownReason::InvalidOperands(node.kind));
                    };
                    values.extend(spread_values);
                }
                _ => return Evaluation::unknown(UnknownReason::UnsupportedSyntax(node.kind)),
            }
        }
        Evaluation {
            outcome: EvaluationOutcome::Value(Value::Object(values)),
            metadata,
        }
    }

    fn evaluate_property(
        &mut self,
        id: NodeId,
        expression: NodeId,
        property: Property,
        optional: bool,
    ) -> Evaluation {
        if !optional && self.is_entity_name_expression(expression) {
            return (self.resolve_entity)(id);
        }
        let base = self.evaluate(expression);
        let mut metadata = base.metadata;
        let base_value = match base.outcome {
            EvaluationOutcome::Value(value) => value,
            EvaluationOutcome::Unknown(_) if self.is_entity_name_expression(expression) => {
                return (self.resolve_entity)(id);
            }
            outcome => return Evaluation { outcome, metadata },
        };
        if optional && matches!(base_value, Value::Null | Value::Undefined) {
            return Evaluation {
                outcome: EvaluationOutcome::Value(Value::Undefined),
                metadata,
            };
        }
        let property_name = match property {
            Property::Node(node) => self.property_node_name(node),
            Property::Expression(expression) => {
                let result = self.evaluate(expression);
                metadata = metadata.merge(result.metadata);
                match result.outcome {
                    EvaluationOutcome::Value(value) => Some(value.js_string()),
                    outcome => return Evaluation { outcome, metadata },
                }
            }
        };
        let Some(property_name) = property_name else {
            return Evaluation::unknown(UnknownReason::InvalidOperands(
                SyntaxKind::PropertyAccessExpression,
            ));
        };
        let value = property_value(&base_value, &property_name);
        Evaluation {
            outcome: EvaluationOutcome::Value(value),
            metadata,
        }
    }

    fn property_node_name(&self, id: NodeId) -> Option<String> {
        match &self.arena.get(id)?.data {
            NodeData::Identifier(data) => Some(data.text.clone()),
            NodeData::StringLiteral(data) => Some(data.text.clone()),
            NodeData::NumericLiteral(data) => Some(Number::from_string(&data.text).to_string()),
            _ => None,
        }
    }

    fn is_entity_name_expression(&self, id: NodeId) -> bool {
        match self.arena.get(id).map(|node| &node.data) {
            Some(NodeData::Identifier(_)) => true,
            Some(NodeData::PropertyAccessExpression(access)) => {
                matches!(
                    self.arena.get(access.name).map(|node| &node.data),
                    Some(NodeData::Identifier(_))
                ) && self.is_entity_name_expression(access.expression)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
enum Property {
    Node(NodeId),
    Expression(NodeId),
}

fn string_evaluation(text: &str) -> Evaluation {
    Evaluation {
        outcome: EvaluationOutcome::Value(Value::String(text.to_owned())),
        metadata: EvaluationMetadata {
            is_syntactically_string: true,
            ..EvaluationMetadata::default()
        },
    }
}

#[allow(clippy::too_many_lines)]
fn binary_value(operator: SyntaxKind, left: &Value, right: &Value) -> Option<Value> {
    if operator == SyntaxKind::PlusToken
        && matches!(left, Value::String(_) | Value::Number(_))
        && matches!(right, Value::String(_) | Value::Number(_))
        && (matches!(left, Value::String(_)) || matches!(right, Value::String(_)))
    {
        return Some(Value::String(format!(
            "{}{}",
            left.js_string(),
            right.js_string()
        )));
    }
    if let (Value::Number(left), Value::Number(right)) = (left, right) {
        let value = match operator {
            SyntaxKind::BarToken => Value::Number(left.bitwise_or(*right)),
            SyntaxKind::AmpersandToken => Value::Number(left.bitwise_and(*right)),
            SyntaxKind::CaretToken => Value::Number(left.bitwise_xor(*right)),
            SyntaxKind::GreaterThanGreaterThanToken => {
                Value::Number(left.signed_right_shift(*right))
            }
            SyntaxKind::GreaterThanGreaterThanGreaterThanToken => {
                Value::Number(left.unsigned_right_shift(*right))
            }
            SyntaxKind::LessThanLessThanToken => Value::Number(left.left_shift(*right)),
            SyntaxKind::AsteriskToken => Value::Number(*left * *right),
            SyntaxKind::SlashToken => Value::Number(*left / *right),
            SyntaxKind::PlusToken => Value::Number(*left + *right),
            SyntaxKind::MinusToken => Value::Number(*left - *right),
            SyntaxKind::PercentToken => Value::Number(left.remainder(*right)),
            SyntaxKind::AsteriskAsteriskToken => Value::Number(left.exponentiate(*right)),
            SyntaxKind::LessThanToken => Value::Boolean(left < right),
            SyntaxKind::LessThanEqualsToken => Value::Boolean(left <= right),
            SyntaxKind::GreaterThanToken => Value::Boolean(left > right),
            SyntaxKind::GreaterThanEqualsToken => Value::Boolean(left >= right),
            SyntaxKind::EqualsEqualsToken | SyntaxKind::EqualsEqualsEqualsToken => {
                Value::Boolean(left == right)
            }
            SyntaxKind::ExclamationEqualsToken | SyntaxKind::ExclamationEqualsEqualsToken => {
                Value::Boolean(left != right)
            }
            _ => return None,
        };
        return Some(value);
    }
    match operator {
        SyntaxKind::EqualsEqualsEqualsToken | SyntaxKind::EqualsEqualsToken => {
            Some(Value::Boolean(left == right))
        }
        SyntaxKind::ExclamationEqualsEqualsToken | SyntaxKind::ExclamationEqualsToken => {
            Some(Value::Boolean(left != right))
        }
        SyntaxKind::LessThanToken
        | SyntaxKind::LessThanEqualsToken
        | SyntaxKind::GreaterThanToken
        | SyntaxKind::GreaterThanEqualsToken
            if matches!(left, Value::String(_)) && matches!(right, Value::String(_)) =>
        {
            let (Value::String(left), Value::String(right)) = (left, right) else {
                unreachable!();
            };
            Some(Value::Boolean(match operator {
                SyntaxKind::LessThanToken => left < right,
                SyntaxKind::LessThanEqualsToken => left <= right,
                SyntaxKind::GreaterThanToken => left > right,
                SyntaxKind::GreaterThanEqualsToken => left >= right,
                _ => unreachable!(),
            }))
        }
        _ => None,
    }
}

fn property_value(value: &Value, property: &str) -> Value {
    match value {
        Value::Object(values) => values.get(property).cloned().unwrap_or(Value::Undefined),
        Value::Array(values) if property == "length" => Value::Number(length_number(values.len())),
        Value::Array(values) => property_index(property)
            .and_then(|index| values.get(index))
            .cloned()
            .unwrap_or(Value::Undefined),
        Value::String(value) if property == "length" => {
            Value::Number(length_number(value.encode_utf16().count()))
        }
        Value::String(value) => property_index(property)
            .and_then(|index| value.encode_utf16().nth(index))
            .and_then(|value| char::from_u32(u32::from(value)))
            .map_or(Value::Undefined, |character| {
                Value::String(character.to_string())
            }),
        _ => Value::Undefined,
    }
}

fn property_index(property: &str) -> Option<usize> {
    let index = property.parse::<usize>().ok()?;
    (index.to_string() == property).then_some(index)
}

fn length_number(length: usize) -> Number {
    Number::from_string(&length.to_string())
}

fn normalize_bigint_literal(text: &str) -> Option<String> {
    let (text, negative) = text
        .strip_prefix('-')
        .map_or((text, false), |text| (text, true));
    let text = text.strip_suffix('n')?;
    let normalized = text.replace('_', "");
    let (radix, digits) = match normalized.get(0..2).unwrap_or_default() {
        "0b" | "0B" => (2, &normalized[2..]),
        "0o" | "0O" => (8, &normalized[2..]),
        "0x" | "0X" => (16, &normalized[2..]),
        _ => (10, normalized.as_str()),
    };
    if digits.is_empty() || !digits.chars().all(|character| character.is_digit(radix)) {
        return None;
    }
    Some(if negative {
        format!("-{normalized}n")
    } else {
        format!("{normalized}n")
    })
}

#[cfg(test)]
mod tests {
    use ts_ast::NodeData;
    use ts_parser::parse_source_file;

    use super::{
        Evaluation, EvaluationError, EvaluationMetadata, EvaluationOutcome, UnknownReason, Value,
        evaluate, evaluate_with,
    };

    fn parse_expression(source: &str) -> (ts_ast::NodeArena, ts_ast::NodeId) {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let source_file = parsed.arena.get(parsed.source_file).unwrap();
        let NodeData::SourceFile(source_file) = &source_file.data else {
            unreachable!()
        };
        let statement = parsed.arena.get(source_file.statements.nodes[0]).unwrap();
        let NodeData::ExpressionStatement(statement) = &statement.data else {
            unreachable!()
        };
        let expression = statement.expression;
        (parsed.arena, expression)
    }

    fn value(source: &str) -> Value {
        let (arena, expression) = parse_expression(source);
        evaluate(&arena, expression).value().unwrap().clone()
    }

    #[test]
    fn evaluates_upstream_numeric_and_string_operations() {
        assert_eq!(value("1 + 2 * 3;"), Value::Number(ts_jsnum::Number(7.0)));
        assert_eq!(value("~1;"), Value::Number(ts_jsnum::Number(-2.0)));
        assert_eq!(value("8 >> 2;"), Value::Number(ts_jsnum::Number(2.0)));
        assert_eq!(value("2 ** 8;"), Value::Number(ts_jsnum::Number(256.0)));
        assert_eq!(value("'value=' + 3;"), Value::String("value=3".into()));
        assert_eq!(
            value("1_000 + 2;"),
            Value::Number(ts_jsnum::Number(1_002.0))
        );
        assert_eq!(
            value("1_000n;"),
            Value::BigInt(ts_jsnum::PseudoBigInt::new("1000", false))
        );
    }

    #[test]
    fn evaluates_conditionals_templates_and_entities() {
        assert_eq!(
            value("false ? 1 : 2;"),
            Value::Number(ts_jsnum::Number(2.0))
        );
        let (arena, expression) = parse_expression("`answer=${answer}`;");
        let result = evaluate_with(&arena, expression, &mut |_| {
            Evaluation::known(Value::Number(ts_jsnum::Number(42.0)))
        });
        assert_eq!(result.value(), Some(&Value::String("answer=42".into())));
        assert!(result.metadata.is_syntactically_string);
    }

    #[test]
    fn evaluates_arrays_objects_and_properties() {
        assert_eq!(value("[1, 2, 3][1];"), Value::Number(ts_jsnum::Number(2.0)));
        assert_eq!(value("({ x: 2 }).x;"), Value::Number(ts_jsnum::Number(2.0)));
        assert_eq!(value("'😀'.length;"), Value::Number(ts_jsnum::Number(2.0)));
        assert_eq!(value("({ x: 1 }).missing;"), Value::Undefined);
    }

    #[test]
    fn distinguishes_unknowns_from_structural_errors() {
        let (arena, expression) = parse_expression("mystery();");
        assert!(matches!(
            evaluate(&arena, expression).outcome,
            EvaluationOutcome::Unknown(UnknownReason::UnsupportedSyntax(_))
        ));
        assert_eq!(
            evaluate(&arena, ts_ast::NodeId::new(u32::MAX)).outcome,
            EvaluationOutcome::Error(EvaluationError::MissingNode(ts_ast::NodeId::new(u32::MAX)))
        );
    }

    #[test]
    fn evaluates_both_operands_and_retains_upstream_binary_metadata() {
        let (arena, expression) = parse_expression("missing + external;");
        let mut resolved = Vec::new();
        let result = evaluate_with(&arena, expression, &mut |reference| {
            let NodeData::Identifier(identifier) = &arena.get(reference).unwrap().data else {
                unreachable!();
            };
            resolved.push(identifier.text.clone());
            if identifier.text == "external" {
                Evaluation {
                    outcome: EvaluationOutcome::Value(Value::String("value".into())),
                    metadata: EvaluationMetadata {
                        is_syntactically_string: true,
                        resolved_other_files: true,
                        has_external_references: true,
                    },
                }
            } else {
                Evaluation::unknown(UnknownReason::UnresolvedEntity(reference))
            }
        });

        assert_eq!(resolved, ["missing", "external"]);
        assert!(matches!(
            result.outcome,
            EvaluationOutcome::Unknown(UnknownReason::UnresolvedEntity(_))
        ));
        assert_eq!(
            result.metadata,
            EvaluationMetadata {
                is_syntactically_string: true,
                resolved_other_files: true,
                has_external_references: true,
            }
        );
    }

    #[test]
    fn prefix_operators_clear_syntactic_string_metadata() {
        let (arena, expression) = parse_expression("+external;");
        let result = evaluate_with(&arena, expression, &mut |_| Evaluation {
            outcome: EvaluationOutcome::Value(Value::Number(ts_jsnum::Number(2.0))),
            metadata: EvaluationMetadata {
                is_syntactically_string: true,
                resolved_other_files: true,
                has_external_references: true,
            },
        });

        assert_eq!(result.value(), Some(&Value::Number(ts_jsnum::Number(2.0))));
        assert_eq!(
            result.metadata,
            EvaluationMetadata {
                is_syntactically_string: false,
                resolved_other_files: true,
                has_external_references: true,
            }
        );
    }

    #[test]
    fn only_resolves_property_access_on_entity_names() {
        let (arena, expression) = parse_expression("factory().value;");
        let mut resolution_count = 0;
        let result = evaluate_with(&arena, expression, &mut |_| {
            resolution_count += 1;
            Evaluation::known(Value::Number(ts_jsnum::Number(42.0)))
        });

        assert_eq!(resolution_count, 0);
        assert!(matches!(
            result.outcome,
            EvaluationOutcome::Unknown(UnknownReason::UnsupportedSyntax(_))
        ));
    }

    #[test]
    fn resolves_qualified_entity_access_without_evaluating_its_receiver() {
        for source in [
            "Namespace.value;",
            "Namespace['value'];",
            "Outer.Inner.value;",
        ] {
            let (arena, expression) = parse_expression(source);
            let mut resolved = Vec::new();
            let result = evaluate_with(&arena, expression, &mut |reference| {
                resolved.push(reference);
                Evaluation::known(Value::Number(ts_jsnum::Number(42.0)))
            });

            assert_eq!(resolved, [expression], "{source}");
            assert_eq!(
                result.value(),
                Some(&Value::Number(ts_jsnum::Number(42.0))),
                "{source}"
            );
        }
    }

    #[test]
    fn successful_element_access_merges_index_metadata() {
        let (arena, expression) = parse_expression("[10, 20][index];");
        let result = evaluate_with(&arena, expression, &mut |_| Evaluation {
            outcome: EvaluationOutcome::Value(Value::Number(ts_jsnum::Number(1.0))),
            metadata: EvaluationMetadata {
                is_syntactically_string: false,
                resolved_other_files: true,
                has_external_references: true,
            },
        });

        assert_eq!(result.value(), Some(&Value::Number(ts_jsnum::Number(20.0))));
        assert!(result.metadata.resolved_other_files);
        assert!(result.metadata.has_external_references);
    }

    #[test]
    fn uses_javascript_array_string_and_index_rules() {
        assert_eq!(
            Value::Array(vec![
                Value::Null,
                Value::Undefined,
                Value::String("x".into())
            ])
            .js_string(),
            ",,x"
        );
        assert_eq!(value("[10, 20]['01'];"), Value::Undefined);
        assert_eq!(value("'ab'['01'];"), Value::Undefined);
    }

    #[test]
    fn failed_template_interpolation_clears_reference_metadata() {
        let (arena, expression) = parse_expression("`${external}${missing}`;");
        let result = evaluate_with(&arena, expression, &mut |reference| {
            let NodeData::Identifier(identifier) = &arena.get(reference).unwrap().data else {
                unreachable!();
            };
            if identifier.text == "external" {
                Evaluation {
                    outcome: EvaluationOutcome::Value(Value::String("value".into())),
                    metadata: EvaluationMetadata {
                        is_syntactically_string: true,
                        resolved_other_files: true,
                        has_external_references: true,
                    },
                }
            } else {
                Evaluation::unknown(UnknownReason::UnresolvedEntity(reference))
            }
        });

        assert!(matches!(
            result.outcome,
            EvaluationOutcome::Unknown(UnknownReason::UnresolvedEntity(_))
        ));
        assert_eq!(
            result.metadata,
            EvaluationMetadata {
                is_syntactically_string: true,
                resolved_other_files: false,
                has_external_references: false,
            }
        );
    }
}
