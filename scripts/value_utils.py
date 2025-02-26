"""Utilities for working with mathematical constant values."""

from sympy.parsing.latex import parse_latex
from sympy import N

class Value:
    """Class representing a mathematical value with multiple representations."""

    def __init__(self, latex_expr):
        self.latex = latex_expr
        self.decimal_approx = self._parse_latex_value(latex_expr)
        patterns = [r'\sqrt', r'\frac', r'\over', r'\pi', r'^{', r'_{']
        if any(pattern in latex_expr for pattern in patterns) and self.decimal_approx is not None:
            # Show decimal approximation for expressions that need it
            self.alt_display = f"≈{self.decimal_approx}"
        elif latex_expr.isdigit() and len(latex_expr) > 4:
            # Show formatted integer for large integers
            self.alt_display = f"{int(latex_expr):,}"
        else:
            self.alt_display = None

    def _parse_latex_value(self, latex_str: str) -> float | None:
        """Parse a LaTeX math expression and return a decimal approximation.
        
        Args:
            latex_str: String containing a LaTeX math expression.
            
        Returns:
            Float approximation of the LaTeX expression or None if expression is too large.
        """
        if latex_str.isdigit():
            return int(latex_str)
        
        # Look for deeply nested exponentials that indicate extremely large numbers
        nested_power_count = latex_str.count("^")
        if nested_power_count > 2:
            # print(f"Warning: Skipping potentially too large expression: {latex_str}")
            return None
            
        try:
            # Remove inequality or approximation symbols
            for symbol in [r'\ge', r'\gt', r'\le', r'\lt', r'\approx', r'{\ge}', r'{\gt}', r'{\le}', r'{\lt}', r'{\approx}']:
                while latex_str.startswith(symbol):
                    latex_str = latex_str[len(symbol):]
            
            expr = parse_latex(latex_str)
            decimal_approx = float(f"{float(N(expr)):.7g}")  # Keep 7 significant digits
            if decimal_approx == float('inf') or decimal_approx == float('-inf'):
                return None
            return decimal_approx
        except Exception as e:
            raise ValueError(f"Error parsing LaTeX expression '{latex_str}': {e}")
        
    def less_than(self, other):
        """Check if this value is less than another value."""
        if self.decimal_approx is None or other.decimal_approx is None:
            return None
        return self.decimal_approx < other.decimal_approx
    
    def to_dict(self):
        """Convert to dict for YAML serialization."""
        return {
            "latex": self.latex,
            "decimal_approx": self.decimal_approx,
            "alt_display": QuotedString(self.alt_display) if self.alt_display is not None else None
        }
    
# Create a custom string class for values that need quotes. e.g. strings that
# are integers with commas are written without quotes, but jekyll interprets
# them as integers and removes the commas.
class QuotedString(str):
    pass
