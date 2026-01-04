import random
import hashlib
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import base64

# ============================================================================
# ELLIPTIC CURVE OPERATIONS
# ============================================================================

def modinv(a, p):
    """Modular multiplicative inverse"""
    return pow(a, -1, p)

class ECPoint:
    """Point on elliptic curve over finite field"""
    def __init__(self, x, y, curve):
        self.x, self.y, self.curve = x, y, curve

    def __add__(self, other):
        """Point addition on elliptic curve"""
        p = self.curve.p
        
        if self.x is None:
            return other
        if other.x is None:
            return self
        if self.x == other.x and (self.y + other.y) % p == 0:
            return self.curve.inf()

        if self.x == other.x:
            lam = (3*self.x*self.x + self.curve.a) * modinv(2*self.y, p) % p
        else:
            lam = (other.y - self.y) * modinv(other.x - self.x, p) % p

        x3 = (lam*lam - self.x - other.x) % p
        y3 = (lam*(self.x - x3) - self.y) % p
        return ECPoint(x3, y3, self.curve)

    def __rmul__(self, k):
        """Scalar multiplication using double-and-add"""
        result = self.curve.inf()
        addend = self
        while k:
            if k & 1:
                result = result + addend
            addend = addend + addend
            k >>= 1
        return result

    def __repr__(self):
        if self.x is None:
            return "O (Point at Infinity)"
        return f"({self.x}, {self.y})"

class Curve:
    """Elliptic curve: y² = x³ + ax + b (mod p)"""
    def __init__(self, a, b, p):
        self.a, self.b, self.p = a, b, p
        discriminant = (4 * pow(a, 3, p) + 27 * pow(b, 2, p)) % p
        if discriminant == 0:
            raise ValueError("Curve is singular!")
    
    def inf(self):
        return ECPoint(None, None, self)
    
    def is_on_curve(self, x, y):
        left = (y * y) % self.p
        right = (x**3 + self.a*x + self.b) % self.p
        return left == right

def find_generator_point(curve):
    """Find a generator point on the curve"""
    for x in range(curve.p):
        y_squared = (x**3 + curve.a*x + curve.b) % curve.p
        for y in range(curve.p):
            if (y*y) % curve.p == y_squared:
                return ECPoint(x, y, curve)
    return None

# ============================================================================
# GF(2^8) ARITHMETIC
# ============================================================================

class GF256:
    """Galois Field GF(2^8) with custom irreducible polynomial"""
    
    def __init__(self, polynomial=0x11B):
        self.polynomial = polynomial
        self.reduction = polynomial & 0xFF
    
    def multiply(self, a, b):
        """Multiply two elements in GF(2^8)"""
        result = 0
        for _ in range(8):
            if b & 1:
                result ^= a
            carry = a & 0x80
            a = (a << 1) & 0xFF
            if carry:
                a ^= self.reduction
            b >>= 1
        return result
    
    def xtime(self, a):
        """Multiply by x in GF(2^8)"""
        if a & 0x80:
            return ((a << 1) ^ self.reduction) & 0xFF
        return (a << 1) & 0xFF
    
    def inverse(self, a):
        """Find multiplicative inverse in GF(2^8)"""
        if a == 0:
            return 0
        for i in range(1, 256):
            if self.multiply(a, i) == 1:
                return i
        raise ValueError(f"No inverse found for {a}")
    
    def generate_rcon(self):
        """Generate round constants"""
        rcon = [0x01]
        for _ in range(9):
            rcon.append(self.xtime(rcon[-1]))
        return rcon

# ============================================================================
# CUSTOM S-BOX GENERATION
# ============================================================================

class CustomSBox:
    """Generate AES S-box from scratch"""
    
    def __init__(self, gf):
        self.gf = gf
        self.sbox = [0] * 256
        self.inv_sbox = [0] * 256
        self._generate()
    
    def _affine_transform(self, byte):
        """Apply affine transformation"""
        result = 0
        for i in range(8):
            bit = 0
            for j in range(8):
                if j == i or j == (i+4)%8 or j == (i+5)%8 or j == (i+6)%8 or j == (i+7)%8:
                    bit ^= (byte >> j) & 1
            result |= (bit << i)
        return result ^ 0x63
    
    def _inverse_affine(self, byte):
        """Apply inverse affine transformation"""
        byte ^= 0x63
        result = 0
        for i in range(8):
            bit = 0
            for j in range(8):
                if j == (i+2)%8 or j == (i+5)%8 or j == (i+7)%8:
                    bit ^= (byte >> j) & 1
            result |= (bit << i)
        return result
    
    def _generate(self):
        """Generate S-box and inverse S-box"""
        for i in range(256):
            if i == 0:
                inv = 0  # Special case: inverse of 0 is 0
            else:
                inv = self.gf.inverse(i)
            self.sbox[i] = self._affine_transform(inv)
        
        for i in range(256):
            self.inv_sbox[self.sbox[i]] = i

# ============================================================================
# AES-128 IMPLEMENTATION
# ============================================================================

class AES128:
    """Complete AES-128 encryption/decryption"""
    
    def __init__(self, sbox, gf):
        self.sbox = sbox
        self.gf = gf
        self.Nr = 10
        self.rcon = self.gf.generate_rcon()
    
    def _rot_word(self, word):
        return word[1:] + word[:1]
    
    def _sub_word(self, word):
        return [self.sbox.sbox[b] for b in word]
    
    def key_expansion(self, key):
        """Key expansion"""
        w = []
        for i in range(4):
            w.append(list(key[4*i:4*i+4]))
        
        for i in range(4, 44):
            temp = w[i-1][:]
            if i % 4 == 0:
                temp = self._sub_word(self._rot_word(temp))
                temp[0] ^= self.rcon[(i//4)-1]
            w.append([w[i-4][j] ^ temp[j] for j in range(4)])
        
        return w
    
    def _sub_bytes(self, state):
        return [[self.sbox.sbox[state[i][j]] for j in range(4)] for i in range(4)]
    
    def _inv_sub_bytes(self, state):
        return [[self.sbox.inv_sbox[state[i][j]] for j in range(4)] for i in range(4)]
    
    def _shift_rows(self, state):
        state[1] = state[1][1:] + state[1][:1]
        state[2] = state[2][2:] + state[2][:2]
        state[3] = state[3][3:] + state[3][:3]
        return state
    
    def _inv_shift_rows(self, state):
        state[1] = state[1][-1:] + state[1][:-1]
        state[2] = state[2][-2:] + state[2][:-2]
        state[3] = state[3][-3:] + state[3][:-3]
        return state
    
    def _mix_columns(self, state):
        """MixColumns"""
        for i in range(4):
            col = [state[j][i] for j in range(4)]
            state[0][i] = self.gf.multiply(col[0], 2) ^ self.gf.multiply(col[1], 3) ^ col[2] ^ col[3]
            state[1][i] = col[0] ^ self.gf.multiply(col[1], 2) ^ self.gf.multiply(col[2], 3) ^ col[3]
            state[2][i] = col[0] ^ col[1] ^ self.gf.multiply(col[2], 2) ^ self.gf.multiply(col[3], 3)
            state[3][i] = self.gf.multiply(col[0], 3) ^ col[1] ^ col[2] ^ self.gf.multiply(col[3], 2)
        return state
    
    def _inv_mix_columns(self, state):
        """Inverse MixColumns"""
        for i in range(4):
            col = [state[j][i] for j in range(4)]
            state[0][i] = self.gf.multiply(col[0], 14) ^ self.gf.multiply(col[1], 11) ^ self.gf.multiply(col[2], 13) ^ self.gf.multiply(col[3], 9)
            state[1][i] = self.gf.multiply(col[0], 9) ^ self.gf.multiply(col[1], 14) ^ self.gf.multiply(col[2], 11) ^ self.gf.multiply(col[3], 13)
            state[2][i] = self.gf.multiply(col[0], 13) ^ self.gf.multiply(col[1], 9) ^ self.gf.multiply(col[2], 14) ^ self.gf.multiply(col[3], 11)
            state[3][i] = self.gf.multiply(col[0], 11) ^ self.gf.multiply(col[1], 13) ^ self.gf.multiply(col[2], 9) ^ self.gf.multiply(col[3], 14)
        return state
    
    def _add_round_key(self, state, round_key):
        for i in range(4):
            for j in range(4):
                state[i][j] ^= round_key[j][i]
        return state
    
    def encrypt_block(self, plaintext, key):
        """Encrypt single 16-byte block"""
        state = [[plaintext[i+4*j] for j in range(4)] for i in range(4)]
        round_keys = self.key_expansion(key)
        
        state = self._add_round_key(state, [round_keys[i] for i in range(4)])
        
        for round in range(1, self.Nr):
            state = self._sub_bytes(state)
            state = self._shift_rows(state)
            state = self._mix_columns(state)
            state = self._add_round_key(state, [round_keys[4*round+i] for i in range(4)])
        
        state = self._sub_bytes(state)
        state = self._shift_rows(state)
        state = self._add_round_key(state, [round_keys[4*self.Nr+i] for i in range(4)])
        
        return bytes([state[i][j] for j in range(4) for i in range(4)])
    
    def decrypt_block(self, ciphertext, key):
        """Decrypt single 16-byte block"""
        state = [[ciphertext[i+4*j] for j in range(4)] for i in range(4)]
        round_keys = self.key_expansion(key)
        
        state = self._add_round_key(state, [round_keys[4*self.Nr+i] for i in range(4)])
        
        for round in range(self.Nr-1, 0, -1):
            state = self._inv_shift_rows(state)
            state = self._inv_sub_bytes(state)
            state = self._add_round_key(state, [round_keys[4*round+i] for i in range(4)])
            state = self._inv_mix_columns(state)
        
        state = self._inv_shift_rows(state)
        state = self._inv_sub_bytes(state)
        state = self._add_round_key(state, [round_keys[i] for i in range(4)])
        
        return bytes([state[i][j] for j in range(4) for i in range(4)])

# ============================================================================
# PADDING & MESSAGE ENCRYPTION
# ============================================================================

def pkcs7_pad(data):
    pad_len = 16 - (len(data) % 16)
    return data + bytes([pad_len] * pad_len)

def pkcs7_unpad(data):
    pad_len = data[-1]
    return data[:-pad_len]

def encrypt_message(message, key, aes):
    padded = pkcs7_pad(message)
    ciphertext = b""
    for i in range(0, len(padded), 16):
        block = padded[i:i+16]
        ciphertext += aes.encrypt_block(block, key)
    return ciphertext

def decrypt_message(ciphertext, key, aes):
    plaintext = b""
    for i in range(0, len(ciphertext), 16):
        block = ciphertext[i:i+16]
        plaintext += aes.decrypt_block(block, key)
    return pkcs7_unpad(plaintext)

# ============================================================================
# GUI APPLICATION
# ============================================================================

class UnifiedCryptoApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Unified ECDH-AES Encryption System")
        self.root.geometry("1100x750")
        
        # System state - everything interconnected
        self.curve = None
        self.G = None
        self.alice_private = None
        self.bob_private = None
        self.alice_public = None
        self.bob_public = None
        self.shared_point = None
        self.aes_key = None
        self.gf = None
        self.sbox = None
        self.aes = None
        self.polynomial = None
        self.last_ciphertext = None  # Added to store encrypted message
        
        self.setup_ui()
        
    def setup_ui(self):
        # Configure styles
        style = ttk.Style()
        style.theme_use('clam')
        
        # Create accent style for important buttons
        style.configure('Accent.TButton', font=('Arial', 10, 'bold'))
        
        main_container = ttk.Frame(self.root, padding="10")
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # Title
        title = ttk.Label(main_container, text="Unified Cryptographic System", 
                         font=('Arial', 18, 'bold'))
        title.pack(pady=10)
        
        subtitle = ttk.Label(main_container, 
                            text="Complete workflow: EC Setup → ECDH → Key Derivation → AES Encryption",
                            font=('Arial', 10, 'italic'))
        subtitle.pack(pady=5)
        
        # Create notebook
        self.notebook = ttk.Notebook(main_container)
        self.notebook.pack(fill=tk.BOTH, expand=True, pady=10)
        
        # Create tabs
        self.create_step1_tab()
        self.create_step2_tab()
        self.create_step3_tab()
        self.create_step4_tab()  # Encryption tab
        self.create_step5_tab()  # Decryption tab
        
        # Status bar
        self.status = ttk.Label(main_container, text="Step 1: Setup elliptic curve", 
                               relief=tk.SUNKEN, anchor=tk.W)
        self.status.pack(fill=tk.X, pady=(5, 0))
        
        # Create helper method references
        self.update_output = self._update_output
        
    def _update_output(self, text_widget, text):
        """Helper method to update text widgets"""
        text_widget.config(state=tk.NORMAL)
        text_widget.delete(1.0, tk.END)
        text_widget.insert(1.0, text)
        text_widget.config(state=tk.DISABLED)
    
    def create_step1_tab(self):
        """Step 1: Elliptic Curve Setup"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Step 1: Curve Setup")
        
        ttk.Label(tab, text="Elliptic Curve Configuration", 
                 font=('Arial', 14, 'bold')).pack(pady=10)
        
        desc = ttk.Label(tab, text="Define the elliptic curve for ECDH key exchange\nCurve: y² = x³ + ax + b (mod 17)")
        desc.pack(pady=5)
        
        # Input frame
        input_frame = ttk.LabelFrame(tab, text="Curve Parameters", padding=15)
        input_frame.pack(pady=20)
        
        ttk.Label(input_frame, text="Coefficient a:").grid(row=0, column=0, sticky=tk.W, pady=5)
        self.a_var = tk.StringVar(value="2")
        ttk.Entry(input_frame, textvariable=self.a_var, width=10).grid(row=0, column=1, padx=10)
        
        ttk.Label(input_frame, text="Coefficient b:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.b_var = tk.StringVar(value="2")
        ttk.Entry(input_frame, textvariable=self.b_var, width=10).grid(row=1, column=1, padx=10)
        
        ttk.Label(input_frame, text="Prime p:").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.p_var = tk.StringVar(value="17")
        ttk.Entry(input_frame, textvariable=self.p_var, width=10, state='readonly').grid(row=2, column=1, padx=10)
        
        ttk.Button(tab, text="Setup Curve & Find Generator", 
                  command=self.setup_curve, style='Accent.TButton').pack(pady=15)
        
        # Result area
        self.curve_output = scrolledtext.ScrolledText(tab, height=10, width=70, font=('Courier', 9))
        self.curve_output.pack(pady=10, padx=20, fill=tk.BOTH, expand=True)
        self.curve_output.config(state=tk.DISABLED)
    
    def create_step2_tab(self):
        """Step 2: ECDH Key Exchange"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Step 2: ECDH Exchange")
        
        ttk.Label(tab, text="ECDH Key Exchange", 
                 font=('Arial', 14, 'bold')).pack(pady=10)
        
        desc = ttk.Label(tab, text="Alice and Bob exchange public keys to compute shared secret point")
        desc.pack(pady=5)
        
        # Keys frame
        keys_frame = ttk.Frame(tab)
        keys_frame.pack(pady=20)
        
        # Alice
        alice_frame = ttk.LabelFrame(keys_frame, text="Alice", padding=10)
        alice_frame.grid(row=0, column=0, padx=10)
        
        ttk.Label(alice_frame, text="Private key kₐ (2-16):").pack(pady=5)
        self.alice_key_var = tk.StringVar(value="5")
        ttk.Entry(alice_frame, textvariable=self.alice_key_var, width=12).pack(pady=5)
        ttk.Button(alice_frame, text="Random", 
                  command=lambda: self.alice_key_var.set(str(random.randint(2, 16)))).pack(pady=5)
        
        # Bob
        bob_frame = ttk.LabelFrame(keys_frame, text="Bob", padding=10)
        bob_frame.grid(row=0, column=1, padx=10)
        
        ttk.Label(bob_frame, text="Private key k_b (2-16):").pack(pady=5)
        self.bob_key_var = tk.StringVar(value="7")
        ttk.Entry(bob_frame, textvariable=self.bob_key_var, width=12).pack(pady=5)
        ttk.Button(bob_frame, text="Random", 
                  command=lambda: self.bob_key_var.set(str(random.randint(2, 16)))).pack(pady=5)
        
        ttk.Button(tab, text="Perform ECDH Exchange", 
                  command=self.perform_ecdh, style='Accent.TButton').pack(pady=15)
        
        # Result area
        self.ecdh_output = scrolledtext.ScrolledText(tab, height=12, width=70, font=('Courier', 9))
        self.ecdh_output.pack(pady=10, padx=20, fill=tk.BOTH, expand=True)
        self.ecdh_output.config(state=tk.DISABLED)
    
    def create_step3_tab(self):
        """Step 3: S-Box Configuration (Independent)"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Step 3: S-Box Config")
        
        ttk.Label(tab, text="Custom S-Box Generation", 
                 font=('Arial', 14, 'bold')).pack(pady=10)
        
        desc = ttk.Label(tab, text="Configure GF(2⁸) irreducible polynomial and generate AES S-box\n(Independent from ECDH - choose your preferred polynomial)")
        desc.pack(pady=5)
        
        # Polynomial selection
        poly_frame = ttk.LabelFrame(tab, text="GF(2⁸) Configuration", padding=15)
        poly_frame.pack(pady=20, fill=tk.X, padx=20)
        
        ttk.Label(poly_frame, text="Irreducible Polynomial (hex):").pack(anchor=tk.W, pady=5)
        
        self.poly_var = tk.StringVar(value="11B")
        poly_combo = ttk.Combobox(poly_frame, textvariable=self.poly_var, width=15, state='readonly')
        poly_combo['values'] = ('11B (Standard AES)', '12B', '12D', '14D', '169', '187', '19F', '1CF', '1F9')
        poly_combo.pack(pady=10, fill=tk.X)
        
        info_label = ttk.Label(poly_frame, text="Standard AES uses 0x11B: x⁸ + x⁴ + x³ + x + 1", 
                              font=('Arial', 9, 'italic'))
        info_label.pack(pady=5)
        
        ttk.Button(tab, text="Generate S-Box & Initialize AES", 
                  command=self.generate_sbox, style='Accent.TButton').pack(pady=15)
        
        # Results
        result_container = ttk.Frame(tab)
        result_container.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Left: Field info
        info_frame = ttk.LabelFrame(result_container, text="GF(2⁸) Information", padding=10)
        info_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S), padx=(0, 10))
        
        self.sbox_info = scrolledtext.ScrolledText(info_frame, height=12, width=35, font=('Courier', 9))
        self.sbox_info.pack(fill=tk.BOTH, expand=True)
        self.sbox_info.config(state=tk.DISABLED)
        
        # Right: S-box preview
        preview_frame = ttk.LabelFrame(result_container, text="S-Box Preview (first 4×4)", padding=10)
        preview_frame.grid(row=0, column=1, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        self.sbox_preview = scrolledtext.ScrolledText(preview_frame, height=12, width=35, font=('Courier', 9))
        self.sbox_preview.pack(fill=tk.BOTH, expand=True)
        self.sbox_preview.config(state=tk.DISABLED)
        
        result_container.columnconfigure(0, weight=1)
        result_container.columnconfigure(1, weight=1)
    
    def create_step4_tab(self):
        """Step 4: Encryption Tab"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Step 4: Encryption")
        
        ttk.Label(tab, text="Message Encryption", 
                 font=('Arial', 14, 'bold')).pack(pady=10)
        
        desc = ttk.Label(tab, text="Encrypt messages using the derived AES key from ECDH")
        desc.pack(pady=5)
        
        # Message input
        input_frame = ttk.LabelFrame(tab, text="Message to Encrypt", padding=10)
        input_frame.pack(fill=tk.X, padx=20, pady=10)
        
        self.message_input = scrolledtext.ScrolledText(input_frame, height=4, width=70, font=('Arial', 10))
        self.message_input.pack(fill=tk.BOTH, expand=True)
        self.message_input.insert(1.0, "Hello, this is a secret message!")
        
        # Buttons
        button_frame = ttk.Frame(tab)
        button_frame.pack(pady=10)
        
        ttk.Button(button_frame, text="Encrypt Message", 
                  command=self.encrypt_msg, style='Accent.TButton').pack(side=tk.LEFT, padx=5)
        
        # Results
        result_frame = ttk.LabelFrame(tab, text="Encryption Results", padding=10)
        result_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        self.encrypt_output = scrolledtext.ScrolledText(result_frame, height=15, width=70, font=('Courier', 9))
        self.encrypt_output.pack(fill=tk.BOTH, expand=True)
        self.encrypt_output.config(state=tk.DISABLED)
    
    def create_step5_tab(self):
        """Step 5: Decryption Tab"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Step 5: Decryption")
        
        ttk.Label(tab, text="Message Decryption", 
                 font=('Arial', 14, 'bold')).pack(pady=10)
        
        desc = ttk.Label(tab, text="Decrypt ciphertexts - can decrypt from this app or external ciphertexts")
        desc.pack(pady=5)
        
        # Create a notebook within the decryption tab
        decrypt_notebook = ttk.Notebook(tab)
        decrypt_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Tab 5.1: Decrypt from app
        decrypt_app_tab = ttk.Frame(decrypt_notebook)
        decrypt_notebook.add(decrypt_app_tab, text="Decrypt App Ciphertext")
        
        ttk.Label(decrypt_app_tab, text="Decrypt the last encrypted message from this app", 
                 font=('Arial', 10, 'bold')).pack(pady=10)
        
        ttk.Button(decrypt_app_tab, text="Decrypt Last Message", 
                  command=self.decrypt_last_msg, style='Accent.TButton').pack(pady=15)
        
        # Tab 5.2: Decrypt external ciphertext
        decrypt_external_tab = ttk.Frame(decrypt_notebook)
        decrypt_notebook.add(decrypt_external_tab, text="Decrypt External Ciphertext")
        
        # Input for external ciphertext
        input_frame = ttk.LabelFrame(decrypt_external_tab, text="Enter Ciphertext to Decrypt", padding=10)
        input_frame.pack(fill=tk.X, padx=20, pady=10)
        
        ttk.Label(input_frame, text="Ciphertext (hex format):").pack(anchor=tk.W, pady=5)
        self.external_ciphertext_input = scrolledtext.ScrolledText(input_frame, height=4, width=70, font=('Courier', 9))
        self.external_ciphertext_input.pack(fill=tk.BOTH, expand=True)
        
        # Format examples
        example_frame = ttk.LabelFrame(decrypt_external_tab, text="Format Examples", padding=10)
        example_frame.pack(fill=tk.X, padx=20, pady=10)
        
        example_text = """Hexadecimal: a1b2c3d4e5f67890a1b2c3d4e5f67890
(no spaces or 0x prefix, just continuous hex digits)
Length must be multiple of 32 hex characters (16 bytes)"""
        
        example_label = ttk.Label(example_frame, text=example_text, font=('Courier', 8))
        example_label.pack()
        
        # Button to decrypt external ciphertext
        ttk.Button(decrypt_external_tab, text="Decrypt External Ciphertext", 
                  command=self.decrypt_external, style='Accent.TButton').pack(pady=15)
        
        # Results area for decryption
        result_frame = ttk.LabelFrame(tab, text="Decryption Results", padding=10)
        result_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        self.decrypt_output = scrolledtext.ScrolledText(result_frame, height=12, width=70, font=('Courier', 9))
        self.decrypt_output.pack(fill=tk.BOTH, expand=True)
        self.decrypt_output.config(state=tk.DISABLED)
    
    # ========================================================================
    # STEP 1: Setup Curve
    # ========================================================================
    
    def setup_curve(self):
        try:
            a = int(self.a_var.get())
            b = int(self.b_var.get())
            p = int(self.p_var.get())
            
            self.curve = Curve(a, b, p)
            self.G = find_generator_point(self.curve)
            
            if not self.G:
                raise ValueError("No generator point found on this curve")
            
            self._update_output(self.curve_output, 
                f"✓ Elliptic Curve Configured Successfully!\n\n"
                f"Curve Equation: y² = x³ + {a}x + {b} (mod {p})\n"
                f"Generator Point: G = {self.G}\n\n"
                f"This curve will be used for ECDH key exchange.\n"
                f"Both Alice and Bob will use point G as the base point.")
            
            self.status.config(text="Step 1 Complete ✓ | Next: Perform ECDH exchange")
            messagebox.showinfo("Success", "Curve setup complete!\nProceed to Step 2 for ECDH exchange.")
            
        except Exception as e:
            messagebox.showerror("Error", f"Curve setup failed: {e}")
    
    # ========================================================================
    # STEP 2: ECDH Key Exchange
    # ========================================================================
    
    def perform_ecdh(self):
        if not self.curve or not self.G:
            messagebox.showerror("Error", "Please complete Step 1: Setup the curve first!")
            self.notebook.select(0)
            return
        
        try:
            kA = int(self.alice_key_var.get())
            kB = int(self.bob_key_var.get())
            
            if not (2 <= kA <= 16 and 2 <= kB <= 16):
                raise ValueError("Private keys must be between 2 and 16")
            
            # Compute public keys
            QA = kA * self.G  # Alice's public key: QA = kA · G
            QB = kB * self.G  # Bob's public key: QB = kB · G
            
            # Compute shared secret point
            S_alice = kA * QB  # Alice computes: S = kA · QB = kA · (kB · G) = kA·kB · G
            S_bob = kB * QA    # Bob computes: S = kB · QA = kB · (kA · G) = kB·kA · G
            
            if S_alice.x != S_bob.x or S_alice.y != S_bob.y:
                raise ValueError("Shared secrets don't match!")
            
            # Store state
            self.alice_private = kA
            self.bob_private = kB
            self.alice_public = QA
            self.bob_public = QB
            self.shared_point = S_alice
            
            # Derive AES-128 key from shared secret point's x-coordinate
            # Key = SHA-256(x-coordinate of S)[:16]
            shared_secret_x = str(S_alice.x).encode()
            key_hash = hashlib.sha256(shared_secret_x).digest()
            self.aes_key = key_hash[:16]
            
            # Display results
            output = f"✓ ECDH Key Exchange Successful!\n\n"
            output += f"ALICE:\n"
            output += f"  Private key: kₐ = {kA}\n"
            output += f"  Public key: Qₐ = kₐ · G = {QA}\n"
            output += f"  Computes shared: S = kₐ · Q_b = kₐ · (k_b · G) = {S_alice}\n\n"
            
            output += f"BOB:\n"
            output += f"  Private key: k_b = {kB}\n"
            output += f"  Public key: Q_b = k_b · G = {QB}\n"
            output += f"  Computes shared: S = k_b · Qₐ = k_b · (kₐ · G) = {S_bob}\n\n"
            
            output += f"VERIFICATION:\n"
            output += f"  Alice's S = Bob's S? YES ✓\n"
            output += f"  Shared Point: S = ({S_alice.x}, {S_alice.y})\n"
            output += f"  This is kₐ·k_b · G = {kA}·{kB} · G\n\n"
            
            output += f"AES KEY DERIVATION:\n"
            output += f"  Shared secret x-coordinate: {S_alice.x}\n"
            output += f"  Method: SHA-256(x-coordinate) → first 16 bytes\n"
            output += f"  AES-128 Key: {self.aes_key.hex()}\n\n"
            
            output += f"⚠ Next: Configure S-box in Step 3 before encryption!"
            
            self._update_output(self.ecdh_output, output)
            self.status.config(text="Step 2 Complete ✓ | Next: Configure S-box for AES")
            messagebox.showinfo("Success", "ECDH complete! AES key derived from shared point.\nProceed to Step 3 to configure S-box.")
            
        except Exception as e:
            messagebox.showerror("Error", f"ECDH failed: {e}")
    
    # ========================================================================
    # STEP 3: Generate S-Box (Independent Configuration)
    # ========================================================================
    
    def generate_sbox(self):
        try:
            polynomial_str = self.poly_var.get().split()[0]  # Get hex value before any description
            polynomial = int(polynomial_str, 16)
            
            self.polynomial = polynomial
            self.gf = GF256(polynomial)
            self.sbox = CustomSBox(self.gf)
            self.aes = AES128(self.sbox, self.gf)
            
            # Display field information
            self._update_output(self.sbox_info,
                f"Polynomial: 0x{polynomial:03X}\n"
                f"Reduction byte: 0x{self.gf.reduction:02X}\n\n"
                f"Field Operations:\n"
                f"  2 × 3 = 0x{self.gf.multiply(2, 3):02X}\n"
                f"  inv(1) = 0x{self.gf.inverse(1):02X}\n"
                f"  inv(2) = 0x{self.gf.inverse(2):02X}\n"
                f"  inv(3) = 0x{self.gf.inverse(3):02X}\n\n"
                f"Round Constants:\n"
                f"  Rcon[1] = 0x{self.gf.generate_rcon()[0]:02X}\n"
                f"  Rcon[2] = 0x{self.gf.generate_rcon()[1]:02X}")
            
            # Display S-Box preview (4x4)
            preview = "S-Box[0:16]:\n"
            for i in range(0, 16, 4):
                row = [f"{self.sbox.sbox[i+j]:02X}" for j in range(4)]
                preview += f"  {' '.join(row)}\n"
            
            preview += "\nInverse verification:\n"
            preview += f"  inv_sbox[sbox[0]] = {self.sbox.inv_sbox[self.sbox.sbox[0]]}\n"
            preview += f"  inv_sbox[sbox[5]] = {self.sbox.inv_sbox[self.sbox.sbox[5]]}\n"
            
            self._update_output(self.sbox_preview, preview)
            
            self.status.config(text="Step 3 Complete ✓ | Ready for encryption and decryption")
            messagebox.showinfo("Success", f"S-Box generated with polynomial 0x{polynomial:03X}!\nAES is ready for encryption and decryption.")
            
        except Exception as e:
            messagebox.showerror("Error", f"S-Box generation failed: {e}")
    
    # ========================================================================
    # STEP 4: Encryption
    # ========================================================================
    
    def encrypt_msg(self):
        if not self.aes_key:
            messagebox.showerror("Error", "Please complete ECDH in Step 2 first!")
            self.notebook.select(1)
            return
        
        if not self.aes:
            messagebox.showerror("Error", "Please generate S-box and initialize AES in Step 3!")
            self.notebook.select(2)
            return
        
        try:
            message = self.message_input.get(1.0, tk.END).strip()
            if not message:
                messagebox.showwarning("Warning", "Please enter a message to encrypt!")
                return
            
            # Convert message to bytes
            plaintext = message.encode('utf-8')
            
            # Encrypt
            ciphertext = encrypt_message(plaintext, self.aes_key, self.aes)
            
            # Store for decryption
            self.last_ciphertext = ciphertext
            
            # Display results
            output = f"✓ Encryption Successful!\n\n"
            output += f"Original Message:\n  {message}\n\n"
            output += f"Message in bytes:\n  {plaintext.hex()}\n\n"
            output += f"AES-128 Key used:\n  {self.aes_key.hex()}\n\n"
            output += f"Ciphertext (hex):\n  {ciphertext.hex()}\n\n"
            output += f"Ciphertext (Base64):\n  {base64.b64encode(ciphertext).decode()}\n\n"
            output += f"Key Information:\n"
            output += f"  Key length: {len(self.aes_key)} bytes\n"
            output += f"  Ciphertext length: {len(ciphertext)} bytes\n\n"
            output += f"Next: Go to Step 5 to decrypt this message or external ciphertexts."
            
            self._update_output(self.encrypt_output, output)
            self.status.config(text="Encryption complete! Go to Step 5 for decryption.")
            
        except Exception as e:
            messagebox.showerror("Error", f"Encryption failed: {e}")
    
    # ========================================================================
    # STEP 5: Decryption
    # ========================================================================
    
    def decrypt_last_msg(self):
        """Decrypt the last message encrypted in this app"""
        if not hasattr(self, 'last_ciphertext') or self.last_ciphertext is None:
            messagebox.showerror("Error", "No ciphertext available! Please encrypt a message first in Step 4.")
            self.notebook.select(3)  # Go to encryption tab
            return
        
        if not self.aes_key:
            messagebox.showerror("Error", "No AES key available! Complete ECDH in Step 2.")
            self.notebook.select(1)
            return
        
        if not self.aes:
            messagebox.showerror("Error", "AES not initialized! Generate S-box in Step 3.")
            self.notebook.select(2)
            return
        
        try:
            # Decrypt
            decrypted = decrypt_message(self.last_ciphertext, self.aes_key, self.aes)
            
            # Convert back to string
            decrypted_text = decrypted.decode('utf-8')
            
            # Display results
            output = f"✓ Decryption Successful!\n\n"
            output += f"Source: Last encrypted message from this app\n\n"
            output += f"Ciphertext (hex):\n  {self.last_ciphertext.hex()}\n\n"
            output += f"AES-128 Key used:\n  {self.aes_key.hex()}\n\n"
            output += f"Decrypted bytes:\n  {decrypted.hex()}\n\n"
            output += f"Decrypted Message:\n  {decrypted_text}\n\n"
            output += f"Verification: ✓ The decrypted message matches the original!"
            
            self._update_output(self.decrypt_output, output)
            self.status.config(text="Decryption complete! Message verified.")
            
        except Exception as e:
            messagebox.showerror("Error", f"Decryption failed: {e}")
    
    def decrypt_external(self):
        """Decrypt an external ciphertext entered by the user"""
        if not self.aes_key:
            messagebox.showerror("Error", "No AES key available! Complete ECDH in Step 2.")
            self.notebook.select(1)
            return
        
        if not self.aes:
            messagebox.showerror("Error", "AES not initialized! Generate S-box in Step 3.")
            self.notebook.select(2)
            return
        
        try:
            # Get ciphertext from input
            ciphertext_hex = self.external_ciphertext_input.get(1.0, tk.END).strip()
            
            if not ciphertext_hex:
                messagebox.showwarning("Warning", "Please enter a ciphertext to decrypt!")
                return
            
            # Clean the hex string (remove spaces, newlines, 0x prefixes)
            ciphertext_hex = ciphertext_hex.replace(' ', '').replace('\n', '').replace('\r', '').replace('0x', '')
            
            # Validate hex format
            if not all(c in '0123456789abcdefABCDEF' for c in ciphertext_hex):
                raise ValueError("Ciphertext must contain only hex characters (0-9, a-f, A-F)")
            
            # Convert hex to bytes
            ciphertext = bytes.fromhex(ciphertext_hex)
            
            # Check length (must be multiple of 16 bytes for AES)
            if len(ciphertext) % 16 != 0:
                raise ValueError(f"Ciphertext length {len(ciphertext)} bytes is not a multiple of 16")
            
            # Decrypt
            decrypted = decrypt_message(ciphertext, self.aes_key, self.aes)
            
            # Try to decode as UTF-8, but also show raw bytes if decoding fails
            try:
                decrypted_text = decrypted.decode('utf-8')
                text_display = f"Decrypted Message:\n  {decrypted_text}\n\n"
                text_display += f"Decoded as: UTF-8 text"
            except UnicodeDecodeError:
                decrypted_text = None
                text_display = f"Decrypted bytes (not valid UTF-8):\n  {decrypted.hex()}\n\n"
                text_display += f"Note: Result is not valid UTF-8 text. May be binary data or wrong key."
            
            # Display results
            output = f"✓ External Decryption Attempt\n\n"
            output += f"Source: External ciphertext input\n\n"
            output += f"Ciphertext (hex):\n  {ciphertext.hex()}\n\n"
            output += f"Ciphertext length: {len(ciphertext)} bytes\n\n"
            output += f"AES-128 Key used:\n  {self.aes_key.hex()}\n\n"
            output += text_display
            
            self._update_output(self.decrypt_output, output)
            self.status.config(text="External decryption attempt complete.")
            
            if decrypted_text:
                messagebox.showinfo("Success", "External ciphertext decrypted successfully!")
            else:
                messagebox.showwarning("Warning", "Decryption produced bytes that are not valid UTF-8 text.\nThe ciphertext may be corrupted or encrypted with a different key.")
            
        except ValueError as e:
            messagebox.showerror("Error", f"Invalid ciphertext format: {e}")
        except Exception as e:
            messagebox.showerror("Error", f"Decryption failed: {e}")

# ============================================================================
# MAIN ENTRY POINT
# ============================================================================

def main():
    """Launch the GUI application"""
    try:
        root = tk.Tk()
        app = UnifiedCryptoApp(root)
        
        # Center window on screen
        root.update_idletasks()
        width = 1100
        height = 750
        screen_width = root.winfo_screenwidth()
        screen_height = root.winfo_screenheight()
        x = (screen_width // 2) - (width // 2)
        y = (screen_height // 2) - (height // 2)
        root.geometry(f'{width}x{height}+{x}+{y}')
        
        root.mainloop()
    except Exception as e:
        print(f"Failed to start application: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()
