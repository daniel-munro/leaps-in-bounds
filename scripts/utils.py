"""Utilities for working with mathematical constant values."""

import os
import requests
import hashlib
from PIL import Image
import io
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


def download_image(url: str, file_extension: str, output_path: str) -> str:
    """Download an image from a URL and save it to a file."""
    try:
        user_agent = 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.3 Safari/605.1.15'
        response = requests.get(url, headers={'User-Agent': user_agent})
        
        if response.status_code == 200:
            # For SVG files, just save as-is
            if file_extension == '.svg':
                with open(output_path, 'wb') as f:
                    f.write(response.content)
            else:
                # Process raster images
                img = Image.open(io.BytesIO(response.content))
                
                # Resize if needed (e.g., max height of 800px)
                max_height = 800
                if img.height > max_height:
                    ratio = max_height / img.height
                    new_size = (int(img.width * ratio), max_height)
                    img = img.resize(new_size, Image.LANCZOS)
                
                # Save with optimization
                img.save(output_path, optimize=True, quality=85)
        else:
            print(f"Failed to download image to {output_path}: {response.status_code}")
    except Exception as e:
        print(f"Error processing image {output_path}: {e}")
        

def process_constant_images(constants: dict) -> None:
    """Process images for constants.
    
    Downloads images, optimizes them, and updates constants with image paths.
    
    Args:
        constants: Dictionary of constants.
    """
    # Create output directory if it doesn't exist
    output_dir = 'assets/images/constants'
    os.makedirs(output_dir, exist_ok=True)
    
    # Process each constant with image data
    for constant_id, data in constants.items():
        if not data or 'image' not in data:
            continue
            
        image_data = data['image']
        source_url = image_data['source_url']
        
        # Determine file extension from URL or default to jpg
        file_extension = os.path.splitext(source_url)[1].lower() or '.jpg'
        if file_extension not in ['.jpg', '.jpeg', '.png', '.gif', '.svg']:
            file_extension = '.jpg'  # Default to jpg for unsupported extensions

        # Generate hash of the URL to use in filename
        url_hash = hashlib.md5(source_url.encode()).hexdigest()[:10]  # First 10 chars of hash for brevity
        output_path = os.path.join(output_dir, f"{constant_id}_{url_hash}{file_extension}")
        
        if not os.path.exists(output_path):
            # Download the image
            print(f"Downloading image for {constant_id} from {source_url}...")
            download_image(source_url, file_extension, output_path)
        
        # Update the constant with the image path
        image_path = f"/{output_path}"
        constants[constant_id]['image']['path'] = image_path
        
        # Remove source_url from the output as we don't need it in the final data
        del constants[constant_id]['image']['source_url']
    
    # print(f"Processed images for constants with image data.")
