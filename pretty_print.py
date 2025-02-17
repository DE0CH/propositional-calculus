import re
import sys

# Your input proof string (s)
s = sys.stdin.read()

# Regular expression to extract statements
pattern = re.compile(r"\|- (.*?) \[(apply|modus_ponens) (.*?)\] ==> (.*)")

# Extract proof steps
proof_steps = []
for match in pattern.finditer(s):
    step = match.group(1).strip()
    rule_type = match.group(2).strip()  # "apply" or "modus_ponens"
    reason = match.group(3).strip()
    label = match.group(4).strip()
    proof_steps.append((step, rule_type, reason, label))

# Determine max widths for alignment
max_step_width = max(len(step) for step, _, _, _ in proof_steps)
max_rule_width = max(len(rule) for _, rule, _, _ in proof_steps)
max_reason_width = max(len(reason) for _, _, reason, _ in proof_steps)

# Generate formatted output
output = []
for step, rule, reason, label in proof_steps:
    output.append(f"|- {step.ljust(max_step_width)}  [{rule.ljust(max_rule_width)} {reason.ljust(max_reason_width)}]  ==> {label}")

# Print the formatted proof
print("\n".join(output))
