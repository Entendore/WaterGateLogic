import sys
import math
import random
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, 
                               QHBoxLayout, QLineEdit, QComboBox, QSlider, QLabel, 
                               QPushButton, QFormLayout, QToolBar, QStatusBar, 
                               QScrollArea, QFrame, QSizePolicy, QToolButton, QDockWidget)
from PySide6.QtCore import Qt, QTimer, QPointF, QRectF, QSize, Signal, QRegularExpression
from PySide6.QtGui import (QPainter, QColor, QPen, QFont, QRadialGradient, 
                           QPainterPath, QLinearGradient, QBrush, QPalette, QKeySequence,
                           QRegularExpressionValidator)

# --- Configuration ---
MIN_WIDTH = 900
MIN_HEIGHT = 600
GRAVITY = 0.25
HISTORY_LEN = 200
SUPPORTED_WIDTHS = [16, 32, 64, 128]

# ============================================================
# DATA CLASSES
# ============================================================

class Particle:
    def __init__(self, x, y, vx, vy, color, p_type='sum', target_slice=-1):
        self.x = x; self.y = y
        self.vx = vx; self.vy = vy
        self.color = color
        self.type = p_type
        self.target_slice = target_slice
        self.life = 1.0
        self.radius = 2.5
        self.trail = []

class Spark:
    def __init__(self, x, y, color):
        self.x = x; self.y = y
        angle = random.uniform(0, 2 * math.pi)
        speed = random.uniform(1.5, 4.5)
        self.vx = math.cos(angle) * speed
        self.vy = math.sin(angle) * speed - 1.0
        self.life = 1.0
        self.color = color

class Ripple:
    def __init__(self, x, y):
        self.x = x; self.y = y
        self.radius = 0
        self.life = 1.0

class ALUSlice:
    def __init__(self, index):
        self.index = index
        self.cin = 0
        self.sum = 0
        self.cout = 0
        self.flash = 0.0
        self.pulse_phase = random.uniform(0, math.pi * 2)
        self.active = False
        self.activity = 0.0

# ============================================================
# VISUALIZER WIDGET
# ============================================================

class VisualizerWidget(QWidget):
    stats_updated = Signal(int, int, float, dict, int)
    bit_width_changed = Signal(int)
    input_changed = Signal()  # Emitted when inputs are modified internally (e.g., clicking LEDs)
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMinimumSize(MIN_WIDTH, MIN_HEIGHT)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.StrongFocus)
        
        # Bit width state
        self.num_bits = 32
        self._rebuild_for_width()
        
        # Operation state
        self.operation = 'ADD'
        self.flow_rate = 4
        self.paused = False
        self.step_mode = False
        self.step_pending = False
        self.time = 0.0
        self.hovered_slice = -1
        
        # Animation timer
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.update_frame)
        self.timer.start(16)
        
        self.setStyleSheet("background-color: #05070A;")

    # --- Bit width management ---
    @property
    def _mask(self):
        return (1 << self.num_bits) - 1
    
    @property
    def _sign_bit_pos(self):
        return self.num_bits - 1
    
    @property
    def _sign_mask(self):
        return 1 << self._sign_bit_pos
    
    def _rebuild_for_width(self):
        """Reset all state for the current bit width."""
        self.slices = [ALUSlice(i) for i in range(self.num_bits)]
        self.activity_map = [0.0] * self.num_bits
        self.bit_history = [0] * HISTORY_LEN
        self.history_idx = 0
        self.history_timer = 0.0
        self.particles = []
        self.sparks = []
        self.ripples = []
        self.flags = {'Z': 0, 'C': 0, 'V': 0, 'N': 0, 'P': 0}
        self.prev_flags = {'Z': 0, 'C': 0, 'V': 0, 'N': 0, 'P': 0}
        self.flag_flash = {'Z': 0, 'C': 0, 'V': 0, 'N': 0, 'P': 0}
        # Default values scaled to width
        self.val_a = self._mask
        self.val_b = 1
        self.frame_count = 0
        self.fps_time = 0.0
        self.current_fps = 60.0
    
    def set_bit_width(self, n):
        """Change the bit width and reset state."""
        if n not in SUPPORTED_WIDTHS:
            return
        self.num_bits = n
        self._rebuild_for_width()
        self.bit_width_changed.emit(n)
        self.update()

    # --- Geometry helpers ---
    def _w(self): return self.width()
    def _h(self): return self.height()
    def _bit_width(self): return self._w() / self.num_bits
    def _slice_y(self): return self._h() * 0.5
    def _pool_y(self): return self._h() * 0.82
    def _slice_x(self, i): return i * self._bit_width() + self._bit_width() / 2
    def _is_compact_mode(self):
        """True when gates are too small for detailed symbols."""
        return self._bit_width() < 18

    # --- Events ---
    def mouseMoveEvent(self, event):
        x = event.position().x()
        self.hovered_slice = int(x / self._bit_width())
        if self.hovered_slice < 0 or self.hovered_slice >= self.num_bits:
            self.hovered_slice = -1
        self.update()

    def leaveEvent(self, event):
        self.hovered_slice = -1
        self.update()

    def mousePressEvent(self, event):
        pos = event.position()
        H = self._h()
        W = self._w()
        led_w = (W - 80) / self.num_bits
        
        # row_idx 0 is A, row_idx 1 is B
        for row_idx, y_pos in enumerate([H * 0.08, H * 0.11]):
            if abs(pos.y() - y_pos) < 10 and pos.x() >= 60:
                bit_idx = int((pos.x() - 60) / led_w)
                if 0 <= bit_idx < self.num_bits:
                    if row_idx == 0:
                        self.val_a ^= (1 << bit_idx)
                    else:
                        self.val_b ^= (1 << bit_idx)
                    self.stats_updated.emit(len(self.particles), self.num_bits, 
                                           self.current_fps, dict(self.flags), self.num_bits)
                    self.input_changed.emit()
                    self.update()
                    return

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Space:
            self.paused = not self.paused
        elif event.key() == Qt.Key_R:
            self.val_a = random.randint(0, self._mask)
            self.val_b = random.randint(0, self._mask)
            self.input_changed.emit()
        elif event.key() == Qt.Key_S:
            self.step_pending = True
        elif event.key() == Qt.Key_Right:
            self.operation = 'SHL'
        elif event.key() == Qt.Key_Left:
            self.operation = 'SHR'
        self.update()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.update()

    # --- Simulation ---
    def update_frame(self):
        if self.paused and not self.step_pending:
            self.update()
            return
        if self.step_pending:
            self.step_pending = False
            self._run_tick()
            self.paused = True
            self.update()
            return
        self._run_tick()
        self.update()

    def _run_tick(self):
        self.time += 0.05
        
        self.frame_count += 1
        self.fps_time += 0.016
        if self.fps_time >= 0.5:
            self.current_fps = self.frame_count / self.fps_time
            self.frame_count = 0
            self.fps_time = 0.0
            self.stats_updated.emit(len(self.particles), self.num_bits, 
                                   self.current_fps, dict(self.flags), self.num_bits)
        
        self.history_timer += 0.016
        if self.history_timer >= 0.05:
            self.history_timer = 0.0
            self.bit_history[self.history_idx] = self.slices[0].sum
            self.history_idx = (self.history_idx + 1) % HISTORY_LEN
        
        # Spawn rate scales with bit width to avoid overload at 128 bits
        spawn_chance = self.flow_rate * 0.08 * (32 / self.num_bits)
        
        for i in range(self.num_bits):
            bit_a = (self.val_a >> i) & 1
            bit_b = (self.val_b >> i) & 1
            if random.random() < spawn_chance:
                if bit_a: self.spawn_input(i, 'a')
                if bit_b: self.spawn_input(i, 'b')
                    
        for p in self.particles[:]: 
            p.trail.append(QPointF(p.x, p.y))
            if len(p.trail) > 6:
                p.trail.pop(0)
                
            if p.type == 'carry':
                p.x += p.vx
                p.y += math.sin(p.x * 0.2) * 0.5
                if p.target_slice < self.num_bits and p.x >= self._slice_x(p.target_slice):
                    self.slices[p.target_slice].flash = 1.0
                    self.slices[p.target_slice].active = True
                    for _ in range(3):
                        self.sparks.append(Spark(p.x, p.y, QColor(255, 200, 0)))
                    self.particles.remove(p)
                    continue
            else:
                p.vy += GRAVITY
                p.x += p.vx
                p.y += p.vy
                p.vx *= 0.95
                
            p.life -= 0.005
            if p.y > self._h() or p.life <= 0:
                self.particles.remove(p)
                continue
                
            if p.type in ['in_a', 'in_b'] and p.y >= self._slice_y() - 5:
                idx = p.target_slice if p.target_slice >= 0 else int(p.x / self._bit_width())
                if 0 <= idx < self.num_bits:
                    self.slices[idx].active = True
                for _ in range(2):
                    self.sparks.append(Spark(p.x, self._slice_y(), p.color))
                self.particles.remove(p)
                
            if p.type == 'sum' and p.y >= self._pool_y():
                self.ripples.append(Ripple(p.x, self._pool_y()))
                self.particles.remove(p)

        for s in self.sparks[:]:
            s.x += s.vx; s.y += s.vy; s.vy += 0.1; s.life -= 0.05
            if s.life <= 0: self.sparks.remove(s)

        for r in self.ripples[:]:
            r.radius += 1.2; r.life -= 0.025
            if r.life <= 0: self.ripples.remove(r)

        # Optimization: pre-calculate active carry targets for O(1) lookups
        active_carry_targets = {p.target_slice for p in self.particles if p.type == 'carry'}

        for i in range(1, self.num_bits):
            self.slices[i].cin = 1 if i in active_carry_targets else 0
        self.slices[0].cin = 1 if self.operation == 'SUB' else 0

        for sl in self.slices:
            sl.activity *= 0.95

        for i, sl in enumerate(self.slices):
            bit_a = (self.val_a >> i) & 1
            bit_b = (self.val_b >> i) & 1
            if self.operation == 'SUB': bit_b = 1 - bit_b
            
            old_sum = sl.sum
            
            if self.operation in ['ADD', 'SUB']:
                total = bit_a + bit_b + sl.cin
                sl.sum = total & 1
                sl.cout = (total >> 1) & 1
            elif self.operation == 'AND':
                sl.sum = bit_a & bit_b; sl.cout = 0
            elif self.operation == 'OR':
                sl.sum = bit_a | bit_b; sl.cout = 0
            elif self.operation == 'XOR':
                sl.sum = bit_a ^ bit_b; sl.cout = 0
            elif self.operation == 'NAND':
                sl.sum = 1 - (bit_a & bit_b); sl.cout = 0
            elif self.operation == 'NOR':
                sl.sum = 1 - (bit_a | bit_b); sl.cout = 0
            elif self.operation == 'XNOR':
                sl.sum = 1 - (bit_a ^ bit_b); sl.cout = 0
            elif self.operation == 'NOT':
                sl.sum = 1 - bit_a; sl.cout = 0
            elif self.operation == 'MUX':
                sl.sum = bit_a if bit_b == 0 else 1 - bit_a; sl.cout = 0
            elif self.operation == 'CMP':
                sl.sum = 1 if bit_a == bit_b else 0; sl.cout = 0
            elif self.operation == 'ABS':
                sign_bit = (self.val_a >> self._sign_bit_pos) & 1
                if sign_bit:
                    inv_a = 1 - bit_a
                    if i == 0:
                        total = inv_a + 1
                        sl.sum = total & 1
                        sl.cout = (total >> 1) & 1
                    else:
                        total = inv_a + sl.cin
                        sl.sum = total & 1
                        sl.cout = (total >> 1) & 1
                else:
                    sl.sum = bit_a; sl.cout = 0
            elif self.operation == 'MIN':
                sl.sum = bit_a if bit_a <= bit_b else bit_b; sl.cout = 0
            elif self.operation == 'MAX':
                sl.sum = bit_a if bit_a >= bit_b else bit_b; sl.cout = 0
            elif self.operation == 'REV':
                src_bit = (self.val_a >> (self.num_bits - 1 - i)) & 1
                sl.sum = src_bit; sl.cout = 0
            elif self.operation == 'POPCNT':
                sl.sum = bit_a; sl.cout = 0
            elif self.operation in ['SHL', 'SHR', 'SAR', 'ROL', 'ROR']:
                sl.sum = bit_a; sl.cout = 0
            elif self.operation == 'INC':
                if i == 0:
                    total = bit_a + 1
                    sl.sum = total & 1
                    sl.cout = (total >> 1) & 1
                else:
                    total = bit_a + sl.cin
                    sl.sum = total & 1
                    sl.cout = (total >> 1) & 1
            elif self.operation == 'DEC':
                bit_b_inv = 1
                if i == 0:
                    total = bit_a + bit_b_inv + 1
                    sl.sum = total & 1
                    sl.cout = (total >> 1) & 1
                else:
                    total = bit_a + bit_b_inv + sl.cin
                    sl.sum = total & 1
                    sl.cout = (total >> 1) & 1
            else:
                sl.sum = bit_a; sl.cout = 0
            
            if sl.sum != old_sum:
                sl.activity = 1.0
            self.activity_map[i] = max(self.activity_map[i], sl.activity)
                
            if sl.sum == 1 and random.random() < spawn_chance * 1.5:
                target_x = self._slice_x(i)
                if self.operation == 'SHL': target_x = self._slice_x((i + 1) % self.num_bits)
                elif self.operation == 'SHR': target_x = self._slice_x((i - 1) % self.num_bits)
                elif self.operation == 'SAR':
                    if i == self.num_bits - 1: target_x = self._slice_x(i)
                    else: target_x = self._slice_x((i - 1) % self.num_bits)
                elif self.operation == 'ROL': target_x = self._slice_x((i + 1) % self.num_bits)
                elif self.operation == 'ROR': target_x = self._slice_x((i - 1) % self.num_bits)
                elif self.operation == 'REV': target_x = self._slice_x(self.num_bits - 1 - i)
                self.spawn_sum(target_x, self._slice_y())
                
            if sl.cout == 1 and i < self.num_bits - 1 and self.operation in ['ADD', 'SUB', 'INC', 'DEC', 'ABS']:
                has_carry = (i + 1) in active_carry_targets
                if not has_carry and random.random() < spawn_chance * 2.0:
                    self.spawn_carry(self._slice_x(i), self._slice_y(), i + 1)
                    
            if sl.flash > 0: sl.flash -= 0.04
            if sl.active and sl.flash <= 0: sl.active = False

        self._update_flags()

    def _update_flags(self):
        res = self._compute_result()
        self.prev_flags = dict(self.flags)
        
        self.flags['Z'] = 1 if res == 0 else 0
        self.flags['N'] = (res >> self._sign_bit_pos) & 1
        low_byte = res & 0xFF
        ones = bin(low_byte).count('1')
        self.flags['P'] = 1 if (ones % 2 == 0) else 0
        
        if self.operation == 'ADD':
            self.flags['C'] = 1 if (self.val_a + self.val_b) > self._mask else 0
        elif self.operation == 'SUB':
            self.flags['C'] = 1 if self.val_a < self.val_b else 0
        elif self.operation in ['INC', 'ABS']:
            self.flags['C'] = self.slices[self.num_bits - 1].cout
        else:
            self.flags['C'] = 0
            
        a_s = self._to_signed(self.val_a)
        b_s = self._to_signed(self.val_b)
        r_s = self._to_signed(res)
        if self.operation in ['ADD', 'SUB', 'INC', 'DEC', 'ABS']:
            if self.operation == 'ADD':
                self.flags['V'] = 1 if ((a_s > 0 and b_s > 0 and r_s < 0) or 
                                        (a_s < 0 and b_s < 0 and r_s > 0)) else 0
            elif self.operation == 'SUB':
                self.flags['V'] = 1 if ((a_s > 0 and b_s < 0 and r_s < 0) or 
                                        (a_s < 0 and b_s > 0 and r_s > 0)) else 0
            elif self.operation == 'INC':
                self.flags['V'] = 1 if (a_s > 0 and r_s < 0) else 0
            elif self.operation == 'DEC':
                self.flags['V'] = 1 if (a_s < 0 and r_s > 0) else 0
            else:
                self.flags['V'] = 0
        else:
            self.flags['V'] = 0
            
        for k in self.flags:
            if self.flags[k] != self.prev_flags[k]:
                self.flag_flash[k] = 1.0
            if self.flag_flash[k] > 0:
                self.flag_flash[k] -= 0.05

    def _to_signed(self, val):
        if val >= self._sign_mask:
            return val - (1 << self.num_bits)
        return val

    def spawn_input(self, bit_index, type_ab):
        x = self._slice_x(bit_index)
        if type_ab == 'a':
            x -= self._bit_width() * 0.25
            color = QColor(0, 255, 255)
        else:
            x += self._bit_width() * 0.25
            color = QColor(255, 0, 255)
        p = Particle(x, self._h() * 0.15, random.uniform(-0.5, 0.5), 
                     random.uniform(2, 4), color, f'in_{type_ab}', bit_index)
        self.particles.append(p)

    def spawn_sum(self, x, y):
        color = QColor(180, 255, 200)
        p = Particle(x, y + 15, random.uniform(-1.5, 1.5), 
                     random.uniform(1, 3), color, 'sum')
        self.particles.append(p)
        
    def spawn_carry(self, x, y, target_slice):
        color = QColor(255, 200, 0)
        p = Particle(x + 10, y, 3.5, 0, color, 'carry', target_slice)
        self.particles.append(p)

    # --- Drawing helpers ---
    def draw_gate_symbol(self, painter, x, y, op, color, scale=1.0):
        painter.save()
        painter.translate(x, y)
        painter.scale(scale, scale)
        
        # Compact mode: draw a simple colored circle instead of detailed path
        if self._is_compact_mode():
            painter.setBrush(color)
            painter.setPen(Qt.NoPen)
            painter.drawEllipse(QPointF(0, 0), 3, 3)
            # Tiny label
            painter.setPen(QColor(255, 255, 255, 180))
            font = QFont('Courier New', 5, QFont.Bold)
            painter.setFont(font)
            short = {'ADD':'+','SUB':'-','AND':'∧','OR':'∨','XOR':'⊕',
                     'NAND':'⊼','NOR':'⊽','XNOR':'⊙','NOT':'¬',
                     'MUX':'M','CMP':'=','SHL':'◀','SHR':'▶',
                     'SAR':'▷','ROL':'↺','ROR':'↻','INC':'++','DEC':'--',
                     'ABS':'|x|','MIN':'↓','MAX':'↑','REV':'⇄','POPCNT':'#'}
            painter.drawText(-4, 2, short.get(op, op[0]))
            painter.restore()
            return
        
        path = QPainterPath()
        w, h = 14, 14
        
        if op in ['ADD', 'SUB']:
            path.moveTo(0, -h/2); path.lineTo(w/2, 0); path.lineTo(0, h/2); path.lineTo(-w/2, 0); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5))
            if op == 'ADD':
                painter.drawLine(-3, 0, 3, 0); painter.drawLine(0, -3, 0, 3)
            else:
                painter.drawLine(-3, 0, 3, 0)
        elif op == 'AND':
            path.moveTo(-w/2, -h/2); path.lineTo(0, -h/2)
            path.arcTo(0, -h/2, w, h, 90, -180); path.lineTo(-w/2, h/2); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
        elif op == 'OR':
            path.moveTo(-w/2, -h/2); path.quadTo(-w/4, 0, -w/2, h/2)
            path.quadTo(w/4, h/2, w/2, 0); path.quadTo(w/4, -h/2, -w/2, -h/2)
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
        elif op == 'XOR':
            path.moveTo(-w/2, -h/2); path.quadTo(-w/4, 0, -w/2, h/2)
            path.quadTo(w/4, h/2, w/2, 0); path.quadTo(w/4, -h/2, -w/2, -h/2)
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            path2 = QPainterPath()
            path2.moveTo(-w/2 - 3, -h/2); path2.quadTo(-w/4 - 3, 0, -w/2 - 3, h/2)
            painter.drawPath(path2)
        elif op == 'NAND':
            path.moveTo(-w/2, -h/2); path.lineTo(0, -h/2)
            path.arcTo(0, -h/2, w, h, 90, -180); path.lineTo(-w/2, h/2); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            painter.setBrush(color); painter.drawEllipse(QPointF(w/2 + 3, 0), 2, 2)
        elif op == 'NOR':
            path.moveTo(-w/2, -h/2); path.quadTo(-w/4, 0, -w/2, h/2)
            path.quadTo(w/4, h/2, w/2, 0); path.quadTo(w/4, -h/2, -w/2, -h/2)
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            painter.setBrush(color); painter.drawEllipse(QPointF(w/2 + 3, 0), 2, 2)
        elif op == 'XNOR':
            path.moveTo(-w/2, -h/2); path.quadTo(-w/4, 0, -w/2, h/2)
            path.quadTo(w/4, h/2, w/2, 0); path.quadTo(w/4, -h/2, -w/2, -h/2)
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            path2 = QPainterPath()
            path2.moveTo(-w/2 - 3, -h/2); path2.quadTo(-w/4 - 3, 0, -w/2 - 3, h/2)
            painter.drawPath(path2)
            painter.setBrush(color); painter.drawEllipse(QPointF(w/2 + 3, 0), 2, 2)
        elif op == 'NOT':
            path.moveTo(-w/2, -h/2); path.lineTo(w/2, 0); path.lineTo(-w/2, h/2); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            painter.setBrush(color); painter.drawEllipse(QPointF(w/2 + 3, 0), 2, 2)
        elif op == 'MUX':
            path.moveTo(-w/2, -h/2); path.lineTo(w/2, -h/4)
            path.lineTo(w/2, h/4); path.lineTo(-w/2, h/2); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            painter.setPen(QPen(color, 1))
            painter.drawLine(-w/4, h/2, 0, 0)
        elif op == 'CMP':
            path.moveTo(0, -h/2); path.lineTo(w/2, 0); path.lineTo(0, h/2); path.lineTo(-w/2, 0); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5))
            painter.drawLine(-3, -2, 3, -2); painter.drawLine(-3, 2, 3, 2)
        elif op in ['SHL', 'SHR', 'SAR', 'ROL', 'ROR']:
            path.moveTo(-w/2, -h/4); path.lineTo(0, -h/4); path.lineTo(0, -h/2)
            path.lineTo(w/2, 0); path.lineTo(0, h/2); path.lineTo(0, h/4); path.lineTo(-w/2, h/4); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            if op == 'SAR':
                painter.setPen(QPen(color, 1))
                painter.drawLine(-w/2 - 2, -h/4, -w/2 - 2, h/4)
        elif op in ['INC', 'DEC']:
            path.addRect(-w/2, -h/2, w, h)
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5))
            if op == 'INC':
                painter.drawLine(-3, 0, 3, 0); painter.drawLine(0, -3, 0, 3)
            else:
                painter.drawLine(-3, 0, 3, 0)
        elif op == 'ABS':
            path.moveTo(-w/2, -h/2); path.lineTo(0, h/2); path.lineTo(w/2, -h/2)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
        elif op == 'MIN':
            path.moveTo(-w/3, -h/2); path.lineTo(w/3, -h/2)
            path.lineTo(w/3, 0); path.lineTo(w/2, 0); path.lineTo(0, h/2)
            path.lineTo(-w/2, 0); path.lineTo(-w/3, 0); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
        elif op == 'MAX':
            path.moveTo(-w/3, h/2); path.lineTo(w/3, h/2)
            path.lineTo(w/3, 0); path.lineTo(w/2, 0); path.lineTo(0, -h/2)
            path.lineTo(-w/2, 0); path.lineTo(-w/3, 0); path.closeSubpath()
            painter.setBrush(QColor(0, 0, 0, 150)); painter.drawPath(path)
            painter.setPen(QPen(color, 1.5)); painter.setBrush(Qt.NoBrush); painter.drawPath(path)
        elif op == 'REV':
            painter.setPen(QPen(color, 1.5))
            painter.drawLine(-w/2, -h/4, w/2, -h/4)
            painter.drawLine(-w/2, h/4, w/2, h/4)
            painter.drawLine(w/2 - 3, -h/4 - 3, w/2, -h/4)
            painter.drawLine(w/2 - 3, -h/4 + 3, w/2, -h/4)
            painter.drawLine(-w/2 + 3, h/4 - 3, -w/2, h/4)
            painter.drawLine(-w/2 + 3, h/4 + 3, -w/2, h/4)
        elif op == 'POPCNT':
            painter.setPen(QPen(color, 1.5))
            painter.drawLine(-w/3, -h/2, -w/3, h/2)
            painter.drawLine(w/3, -h/2, w/3, h/2)
            painter.drawLine(-w/2, -h/3, w/2, -h/3)
            painter.drawLine(-w/2, h/3, w/2, h/3)
        painter.restore()

    def draw_led_register(self, painter, y, value, color_on, color_off, label, show_hex=True):
        painter.setPen(QColor(150, 180, 220))
        font = QFont('Courier New', 10, QFont.Bold)
        painter.setFont(font)
        painter.drawText(10, y + 5, label)
        
        start_x = 60
        led_w = (self._w() - 80) / self.num_bits
        compact = self._is_compact_mode()
        
        for i in range(self.num_bits):
            bit = (value >> i) & 1
            cx = start_x + i * led_w + led_w / 2
            if bit:
                if not compact:
                    glow = QRadialGradient(cx, y, led_w)
                    glow.setColorAt(0, QColor(color_on.red(), color_on.green(), color_on.blue(), 100))
                    glow.setColorAt(1, QColor(0, 0, 0, 0))
                    painter.setPen(Qt.NoPen); painter.setBrush(glow)
                    painter.drawEllipse(QPointF(cx, y), led_w, led_w)
                painter.setBrush(color_on)
            else:
                painter.setBrush(color_off)
            painter.setPen(Qt.NoPen)
            radius = 3 if not compact else 2
            painter.drawEllipse(QPointF(cx, y), radius, radius)
            
        if show_hex:
            hex_chars = self.num_bits // 4
            hex_val = f"0x{value:0{hex_chars}X}"
            painter.setPen(QColor(150, 180, 220))
            painter.setFont(QFont('Courier New', 8, QFont.Bold))
            # Position hex value at the end of the register row
            text_x = int(start_x + self.num_bits * led_w + 10)
            if text_x + len(hex_val) * 7 < self._w():
                painter.drawText(text_x, y + 5, hex_val)

    def draw_flags_register(self, painter, x, y):
        flags_data = [
            ('Z', self.flags['Z'], QColor(100, 200, 255)),
            ('C', self.flags['C'], QColor(255, 200, 100)),
            ('V', self.flags['V'], QColor(255, 100, 150)),
            ('N', self.flags['N'], QColor(200, 100, 255)),
            ('P', self.flags['P'], QColor(100, 255, 200)),
        ]
        
        box_w = 180
        box_h = 90
        painter.setBrush(QColor(10, 15, 30, 220))
        painter.setPen(QPen(QColor(60, 80, 120), 1))
        painter.drawRoundedRect(x, y, box_w, box_h, 4, 4)
        
        painter.setPen(QColor(150, 180, 220))
        font = QFont('Courier New', 9, QFont.Bold)
        painter.setFont(font)
        painter.drawText(x + 8, y + 14, "FLAGS")
        
        painter.setPen(QPen(QColor(100, 150, 255, 150), 1))
        for cx, cy, dx, dy in [(x, y, 1, 1), (x+box_w, y, -1, 1),
                                (x, y+box_h, 1, -1), (x+box_w, y+box_h, -1, -1)]:
            painter.drawLine(int(cx), int(cy), int(cx + 4*dx), int(cy))
            painter.drawLine(int(cx), int(cy), int(cx), int(cy + 4*dy))
        
        font_small = QFont('Courier New', 8, QFont.Bold)
        painter.setFont(font_small)
        
        for idx, (name, val, color) in enumerate(flags_data):
            fx = x + 10 + (idx % 3) * 55
            fy = y + 35 + (idx // 3) * 28
            flash = self.flag_flash.get(name, 0)
            
            if val:
                glow = QRadialGradient(fx, fy, 10)
                glow.setColorAt(0, QColor(color.red(), color.green(), color.blue(), 150))
                glow.setColorAt(1, QColor(0, 0, 0, 0))
                painter.setPen(Qt.NoPen); painter.setBrush(glow)
                painter.drawEllipse(QPointF(fx, fy), 10, 10)
                painter.setBrush(color)
            else:
                painter.setBrush(QColor(30, 40, 50))
            painter.setPen(Qt.NoPen)
            painter.drawEllipse(QPointF(fx, fy), 4, 4)
            
            painter.setPen(QColor(200, 220, 255))
            painter.drawText(int(fx + 8), int(fy + 3), name)
            
            if flash > 0:
                flash_col = QColor(255, 255, 255, int(100 * flash))
                painter.setPen(Qt.NoPen)
                painter.setBrush(flash_col)
                painter.drawEllipse(QPointF(fx, fy), 6, 6)

    def draw_activity_heatmap(self, painter, y, h):
        for i in range(self.num_bits):
            x = i * self._bit_width()
            intensity = self.activity_map[i]
            if intensity > 0.05:
                col = QColor(255, int(100 * (1 - intensity)), 0, int(180 * intensity))
                painter.fillRect(int(x), int(y), int(self._bit_width()) + 1, int(h), col)

    def draw_oscilloscope(self, painter, x, y, w, h):
        painter.setBrush(QColor(5, 10, 20, 200))
        painter.setPen(QPen(QColor(60, 80, 120), 1))
        painter.drawRoundedRect(x, y, w, h, 3, 3)
        
        painter.setPen(QPen(QColor(30, 40, 60), 1))
        for gx in range(5):
            px = x + (gx * w / 4)
            painter.drawLine(int(px), int(y), int(px), int(y + h))
        for gy in range(3):
            py = y + (gy * h / 2)
            painter.drawLine(int(x), int(py), int(x + w), int(py))
        
        painter.setPen(QColor(100, 200, 255))
        font = QFont('Courier New', 8, QFont.Bold)
        painter.setFont(font)
        painter.drawText(int(x + 4), int(y + 10), "BIT[0] SCOPE")
        
        painter.setPen(QPen(QColor(0, 255, 200), 1.5))
        margin = 14
        plot_h = h - margin - 4
        plot_w = w - 8
        
        for i in range(HISTORY_LEN - 1):
            idx1 = (self.history_idx + i) % HISTORY_LEN
            idx2 = (self.history_idx + i + 1) % HISTORY_LEN
            v1 = self.bit_history[idx1]
            v2 = self.bit_history[idx2]
            x1 = x + 4 + (i * plot_w / HISTORY_LEN)
            x2 = x + 4 + ((i + 1) * plot_w / HISTORY_LEN)
            y1 = y + margin + (1 - v1) * plot_h
            y2 = y + margin + (1 - v2) * plot_h
            painter.drawLine(int(x1), int(y1), int(x2), int(y2))

    def draw_connection_pipes(self, painter):
        SLICE_Y = self._slice_y()
        H = self._h()
        phase = (self.time * 2) % 1.0
        
        painter.setPen(QPen(QColor(0, 255, 255, 80), 2))
        for i in range(self.num_bits):
            x = self._slice_x(i) - self._bit_width() * 0.25
            y_start = H * 0.08
            y_end = SLICE_Y - 20
            painter.drawLine(int(x), int(y_start + 5), int(x), int(y_end))
        
        painter.setPen(QPen(QColor(255, 0, 255, 80), 2))
        for i in range(self.num_bits):
            x = self._slice_x(i) + self._bit_width() * 0.25
            y_start = H * 0.11
            y_end = SLICE_Y - 20
            painter.drawLine(int(x), int(y_start + 5), int(x), int(y_end))
        
        if not self.paused:
            painter.setPen(Qt.NoPen)
            for i in range(self.num_bits):
                x_a = self._slice_x(i) - self._bit_width() * 0.25
                y_a = H * 0.08 + 5 + (phase * (SLICE_Y - 20 - H * 0.08 - 5))
                bit_a = (self.val_a >> i) & 1
                if bit_a:
                    painter.setBrush(QColor(0, 255, 255, 200))
                    painter.drawEllipse(QPointF(x_a, y_a), 2, 2)
                
                x_b = self._slice_x(i) + self._bit_width() * 0.25
                y_b = H * 0.11 + 5 + (phase * (SLICE_Y - 20 - H * 0.11 - 5))
                bit_b = (self.val_b >> i) & 1
                if bit_b:
                    painter.setBrush(QColor(255, 0, 255, 200))
                    painter.drawEllipse(QPointF(x_b, y_b), 2, 2)

    # --- Main paint ---
    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        painter.setRenderHint(QPainter.SmoothPixmapTransform)
        
        W, H = self._w(), self._h()
        SLICE_Y = self._slice_y()
        POOL_Y = self._pool_y()
        
        bg_grad = QLinearGradient(0, 0, 0, H)
        bg_grad.setColorAt(0, QColor(5, 5, 15))
        bg_grad.setColorAt(1, QColor(10, 15, 30))
        painter.fillRect(self.rect(), bg_grad)
        
        painter.setPen(QPen(QColor(20, 30, 50), 1))
        for i in range(self.num_bits + 1):
            x = i * self._bit_width()
            painter.drawLine(int(x), int(H * 0.13), int(x), int(POOL_Y))

        self.draw_connection_pipes(painter)

        clock_phase = (self.time * 3) % 2.0
        clock_y = H * 0.03 if clock_phase < 1.0 else H * 0.06
        painter.setPen(QPen(QColor(100, 150, 255), 2))
        painter.drawLine(10, H * 0.045, 10, clock_y)
        for i in range(1, 20):
            next_y = H * 0.03 if (i % 2) == 0 else H * 0.06
            painter.drawLine(10 + i * 15, clock_y, 10 + i * 15, next_y)
            clock_y = next_y
        painter.drawLine(10 + 20 * 15, clock_y, W - 10, clock_y)
        painter.setPen(QColor(100, 150, 255))
        painter.setFont(QFont('Courier New', 10))
        painter.drawText(W - 100, H * 0.05, "CLK")

        self.draw_led_register(painter, H * 0.08, self.val_a, QColor(0, 255, 255), QColor(20, 40, 50), "IN A")
        self.draw_led_register(painter, H * 0.11, self.val_b, QColor(255, 0, 255), QColor(40, 20, 50), "IN B")

        self.draw_activity_heatmap(painter, SLICE_Y - 30, 8)

        # Carry bus - skip detailed drawing at very high bit counts for performance
        if not self._is_compact_mode():
            active_carry_targets = {p.target_slice for p in self.particles if p.type == 'carry'}
            for i in range(self.num_bits - 1):
                x1 = self._slice_x(i) + 10
                x2 = self._slice_x(i+1) - 10
                carry_active = (i + 1) in active_carry_targets
                painter.setPen(QPen(QColor(40, 30, 10), 4))
                painter.drawLine(int(x1), int(SLICE_Y), int(x2), int(SLICE_Y))
                if carry_active:
                    painter.setPen(QPen(QColor(255, 200, 0, 200), 3))
                    painter.drawLine(int(x1), int(SLICE_Y), int(x2), int(SLICE_Y))
                    painter.setPen(QPen(QColor(255, 255, 200), 1))
                    painter.drawLine(int(x1), int(SLICE_Y), int(x2), int(SLICE_Y))
        else:
            # Simple bus line for compact mode
            painter.setPen(QPen(QColor(40, 30, 10), 2))
            painter.drawLine(0, int(SLICE_Y), W, int(SLICE_Y))

        for sl in self.slices:
            sl_x = self._slice_x(sl.index)
            bw = self._bit_width()
            housing_w = bw * 0.8
            housing_h = 40 if not self._is_compact_mode() else 28
            hx = sl_x - housing_w / 2
            hy = SLICE_Y - housing_h / 2
            
            housing_col = QColor(15, 20, 35, 220)
            if sl.flash > 0: housing_col = QColor(40, 60, 100, 220)
            painter.setBrush(housing_col)
            painter.setPen(QPen(QColor(40, 60, 100), 1))
            painter.drawRoundedRect(QRectF(hx, hy, housing_w, housing_h), 3, 3)
            
            if not self._is_compact_mode():
                painter.setPen(QPen(QColor(80, 120, 200, 150), 1))
                b_len = 4
                for cx, cy, dx, dy in [(hx, hy, 1, 1), (hx+housing_w, hy, -1, 1),
                                        (hx, hy+housing_h, 1, -1), (hx+housing_w, hy+housing_h, -1, -1)]:
                    painter.drawLine(int(cx), int(cy), int(cx + b_len*dx), int(cy))
                    painter.drawLine(int(cx), int(cy), int(cx), int(cy + b_len*dy))

                painter.setPen(Qt.NoPen)
                painter.setBrush(QColor(0, 255, 255, 100))
                painter.drawEllipse(QPointF(sl_x - 6, hy + 4), 2, 2)
                painter.setBrush(QColor(255, 0, 255, 100))
                painter.drawEllipse(QPointF(sl_x + 6, hy + 4), 2, 2)

            core_color = self._get_op_color()
            
            pulse = 0.5 + 0.5 * math.sin(self.time * 2 + sl.pulse_phase)
            if sl.active or sl.flash > 0: pulse = 1.0
            final_col = QColor(core_color.red(), core_color.green(), core_color.blue(), int(150 + 105 * pulse))
            
            if sl.active or sl.flash > 0:
                glow_grad = QRadialGradient(sl_x, SLICE_Y, 20)
                glow_grad.setColorAt(0, QColor(core_color.red(), core_color.green(), core_color.blue(), 100))
                glow_grad.setColorAt(1, QColor(0, 0, 0, 0))
                painter.setBrush(glow_grad); painter.setPen(Qt.NoPen)
                painter.drawEllipse(QPointF(sl_x, SLICE_Y), 20, 20)

            self.draw_gate_symbol(painter, sl_x, SLICE_Y, self.operation, final_col, 
                                 1.2 if not self._is_compact_mode() else 0.9)

            sum_col = QColor(180, 255, 200) if sl.sum == 1 else QColor(30, 40, 50)
            painter.setBrush(sum_col); painter.setPen(Qt.NoPen)
            painter.drawEllipse(QPointF(sl_x, hy + housing_h - 4), 2, 2)
            
            cout_col = QColor(255, 200, 0) if sl.cout == 1 else QColor(40, 30, 10)
            painter.setBrush(cout_col)
            painter.drawEllipse(QPointF(hx + housing_w - 4, SLICE_Y), 2, 2)

        pool_grad = QLinearGradient(0, POOL_Y, 0, H)
        pool_grad.setColorAt(0, QColor(10, 30, 40, 150))
        pool_grad.setColorAt(1, QColor(5, 15, 25, 250))
        painter.fillRect(0, int(POOL_Y), W, int(H - POOL_Y), pool_grad)
        painter.setPen(QPen(QColor(0, 255, 255, 100), 1))
        painter.drawLine(0, int(POOL_Y), W, int(POOL_Y))

        painter.setCompositionMode(QPainter.CompositionMode_Plus)
        for p in self.particles:
            if len(p.trail) > 1:
                for i in range(len(p.trail) - 1):
                    alpha = int(150 * (i / len(p.trail)))
                    col = QColor(p.color.red(), p.color.green(), p.color.blue(), alpha)
                    painter.setPen(QPen(col, 2))
                    painter.drawLine(p.trail[i], p.trail[i+1])
            grad = QRadialGradient(p.x, p.y, p.radius * 4)
            col_core = QColor(p.color.red(), p.color.green(), p.color.blue(), 255)
            col_edge = QColor(p.color.red(), p.color.green(), p.color.blue(), 0)
            grad.setColorAt(0, col_core); grad.setColorAt(1, col_edge)
            painter.setBrush(grad); painter.setPen(Qt.NoPen)
            painter.drawEllipse(QPointF(p.x, p.y), p.radius * 4, p.radius * 4)
            
        for s in self.sparks:
            alpha = int(255 * s.life)
            col = QColor(s.color.red(), s.color.green(), s.color.blue(), alpha)
            painter.setPen(QPen(col, 1.5))
            painter.drawLine(QPointF(s.x, s.y), QPointF(s.x - s.vx * 2, s.y - s.vy * 2))
            
        for r in self.ripples:
            alpha = int(150 * r.life)
            col = QColor(180, 255, 200, alpha)
            painter.setPen(QPen(col, 1.5)); painter.setBrush(Qt.NoBrush)
            painter.drawEllipse(QPointF(r.x, r.y), r.radius, r.radius * 0.3)
            
        painter.setCompositionMode(QPainter.CompositionMode_SourceOver)
        
        res = self._compute_result()
        self.draw_led_register(painter, H * 0.88, res, QColor(180, 255, 200), QColor(20, 40, 30), "OUT ")
        
        painter.setPen(QColor(200, 220, 255))
        painter.setFont(QFont('Courier New', 14, QFont.Bold))
        hex_str = f"0x{res:0{(self.num_bits // 4)}X}"
        painter.drawText(10, int(H - 15), hex_str)

        self.draw_flags_register(painter, W - 200, 10)
        self.draw_oscilloscope(painter, W - 200, H - 100, 190, 85)
        
        if self.hovered_slice >= 0:
            i = self.hovered_slice
            sl = self.slices[i]
            bx = self._slice_x(i) + 25
            by = SLICE_Y - 70
            if bx + 130 > W: bx = self._slice_x(i) - 155
            
            painter.setBrush(QColor(10, 15, 30, 230))
            painter.setPen(QPen(QColor(100, 150, 255), 1))
            painter.drawRoundedRect(bx, by, 130, 80, 4, 4)
            
            painter.setPen(QColor(200, 220, 255))
            font = QFont('Courier New', 10, QFont.Bold)
            painter.setFont(font)
            painter.drawText(int(bx + 10), int(by + 18), f"BIT [{i:02d}]")
            font.setBold(False); painter.setFont(font)
            bit_a = (self.val_a >> i) & 1
            bit_b = (self.val_b >> i) & 1
            if self.operation == 'SUB': bit_b = 1 - bit_b
            painter.drawText(int(bx + 10), int(by + 35), f"A: {bit_a}   B: {bit_b}")
            painter.drawText(int(bx + 10), int(by + 50), f"Cin: {sl.cin}")
            painter.drawText(int(bx + 10), int(by + 65), f"Sum: {sl.sum}  Cout: {sl.cout}")

        painter.setPen(QPen(QColor(0, 0, 0, 25), 1))
        for y in range(0, H, 4):
            painter.drawLine(0, y, W, y)

    def _get_op_color(self):
        colors = {
            'ADD': QColor(0, 255, 200), 'SUB': QColor(255, 100, 150),
            'AND': QColor(100, 255, 100), 'OR': QColor(255, 150, 50),
            'XOR': QColor(200, 100, 255), 'NAND': QColor(150, 255, 100),
            'NOR': QColor(255, 200, 100), 'XNOR': QColor(255, 150, 200),
            'NOT': QColor(255, 100, 100), 'MUX': QColor(100, 200, 255),
            'CMP': QColor(255, 255, 100), 'SHL': QColor(100, 200, 255),
            'SHR': QColor(100, 200, 255), 'SAR': QColor(150, 200, 255),
            'ROL': QColor(200, 150, 255), 'ROR': QColor(200, 150, 255),
            'INC': QColor(100, 255, 200), 'DEC': QColor(255, 150, 150),
            'ABS': QColor(255, 200, 100), 'MIN': QColor(100, 200, 255),
            'MAX': QColor(255, 100, 200), 'REV': QColor(200, 200, 100),
            'POPCNT': QColor(150, 255, 150),
        }
        return colors.get(self.operation, QColor(100, 150, 255))

    def _compute_result(self):
        mask = self._mask
        if self.operation == 'ADD': return (self.val_a + self.val_b) & mask
        elif self.operation == 'SUB': return (self.val_a - self.val_b) & mask
        elif self.operation == 'AND': return self.val_a & self.val_b
        elif self.operation == 'OR': return self.val_a | self.val_b
        elif self.operation == 'XOR': return self.val_a ^ self.val_b
        elif self.operation == 'NAND': return ~(self.val_a & self.val_b) & mask
        elif self.operation == 'NOR': return ~(self.val_a | self.val_b) & mask
        elif self.operation == 'XNOR': return ~(self.val_a ^ self.val_b) & mask
        elif self.operation == 'NOT': return ~self.val_a & mask
        elif self.operation == 'MUX':
            result = 0
            for i in range(self.num_bits):
                bit_a = (self.val_a >> i) & 1
                bit_b = (self.val_b >> i) & 1
                result |= ((bit_a if bit_b == 0 else 1 - bit_a) << i)
            return result
        elif self.operation == 'CMP':
            result = 0
            for i in range(self.num_bits):
                if ((self.val_a >> i) & 1) == ((self.val_b >> i) & 1):
                    result |= (1 << i)
            return result
        elif self.operation == 'ABS':
            if self.val_a >= self._sign_mask:
                return ((~self.val_a) + 1) & mask
            return self.val_a
        elif self.operation == 'MIN':
            return self.val_a if self._to_signed(self.val_a) <= self._to_signed(self.val_b) else self.val_b
        elif self.operation == 'MAX':
            return self.val_a if self._to_signed(self.val_a) >= self._to_signed(self.val_b) else self.val_b
        elif self.operation == 'REV':
            result = 0
            for i in range(self.num_bits):
                if (self.val_a >> i) & 1:
                    result |= (1 << (self.num_bits - 1 - i))
            return result
        elif self.operation == 'POPCNT':
            return bin(self.val_a).count('1')
        elif self.operation == 'SHL': return (self.val_a << 1) & mask
        elif self.operation == 'SHR': return (self.val_a >> 1) & mask
        elif self.operation == 'SAR':
            sign_bit = (self.val_a >> self._sign_bit_pos) & 1
            result = (self.val_a >> 1) & (self._mask >> 1)
            if sign_bit: result |= self._sign_mask
            return result
        elif self.operation == 'ROL':
            return ((self.val_a << 1) | (self.val_a >> self._sign_bit_pos)) & mask
        elif self.operation == 'ROR':
            return ((self.val_a >> 1) | ((self.val_a & 1) << self._sign_bit_pos)) & mask
        elif self.operation == 'INC': return (self.val_a + 1) & mask
        elif self.operation == 'DEC': return (self.val_a - 1) & mask
        return 0


# ============================================================
# COLLAPSIBLE GROUP BOX
# ============================================================

class CollapsibleBox(QWidget):
    def __init__(self, title, parent=None):
        super().__init__(parent)
        self.main_layout = QVBoxLayout(self)
        self.main_layout.setContentsMargins(0, 0, 0, 0)
        self.main_layout.setSpacing(0)
        
        self.toggle_btn = QToolButton(self)
        self.toggle_btn.setStyleSheet("""
            QToolButton {
                background-color: #1a1f35;
                color: #8ab4ff;
                border: 1px solid #2a3555;
                border-radius: 4px;
                padding: 8px;
                font-weight: bold;
                font-family: 'Courier New';
            }
            QToolButton:hover { background-color: #252b45; }
        """)
        self.toggle_btn.setText(title)
        self.toggle_btn.setCheckable(True)
        self.toggle_btn.setChecked(True)
        self.toggle_btn.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toggle_btn.setArrowType(Qt.DownArrow)
        self.toggle_btn.toggled.connect(self._on_toggled)
        
        self.content_area = QWidget(self)
        self.content_area.setStyleSheet("background-color: #0d1020;")
        self.content_layout = QVBoxLayout(self.content_area)
        self.content_layout.setContentsMargins(8, 8, 8, 8)
        self.content_layout.setSpacing(6)
        
        self.main_layout.addWidget(self.toggle_btn)
        self.main_layout.addWidget(self.content_area)

    def _on_toggled(self, checked):
        self.content_area.setVisible(checked)
        self.toggle_btn.setArrowType(Qt.DownArrow if checked else Qt.RightArrow)


# ============================================================
# MAIN WINDOW
# ============================================================

class ALUWaterfall(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("32-Bit ALU Waterfall Visualizer — Ultimate Edition")
        self.resize(1400, 900)
        self.setMinimumSize(MIN_WIDTH + 300, MIN_HEIGHT)
        
        self.visualizer = VisualizerWidget()
        self.setCentralWidget(self.visualizer)
        
        self._build_toolbar()
        self._build_side_panel()
        self._build_status_bar()
        self._apply_theme()
        self._connect_signals()

    def _build_toolbar(self):
        toolbar = QToolBar("Main Toolbar", self)
        toolbar.setMovable(False)
        toolbar.setIconSize(QSize(20, 20))
        toolbar.setStyleSheet("""
            QToolBar {
                background-color: #0d1020;
                border-bottom: 1px solid #2a3555;
                padding: 4px;
                spacing: 8px;
            }
            QToolButton, QPushButton {
                background-color: #1a1f35;
                color: #e0e8ff;
                border: 1px solid #2a3555;
                border-radius: 4px;
                padding: 6px 12px;
                font-family: 'Courier New';
                font-weight: bold;
            }
            QPushButton:hover { background-color: #252b45; border-color: #4a6aaa; }
            QComboBox {
                background-color: #1a1f35;
                color: #0ff;
                border: 1px solid #2a3555;
                border-radius: 4px;
                padding: 4px 8px;
                font-family: 'Courier New';
                min-width: 80px;
            }
            QComboBox:hover { border-color: #4a6aaa; }
            QComboBox QAbstractItemView {
                background-color: #1a1f35;
                color: #e0e8ff;
                selection-background-color: #3a4a7a;
            }
        """)
        
        title_label = QLabel("  ◆  ALU WATERFALL  ◆  ")
        title_label.setStyleSheet("color: #8ab4ff; font-weight: bold; font-family: 'Courier New'; font-size: 13px;")
        toolbar.addWidget(title_label)
        toolbar.addSeparator()
        
        # === BIT WIDTH SELECTOR ===
        width_label = QLabel(" WIDTH: ")
        width_label.setStyleSheet("color: #8ab4ff; font-family: 'Courier New'; font-weight: bold;")
        toolbar.addWidget(width_label)
        self.combo_width = QComboBox()
        self.combo_width.addItems(['16', '32', '64', '128'])
        self.combo_width.setCurrentText('32')
        self.combo_width.setStyleSheet(self.combo_width.styleSheet() + "min-width: 70px;")
        toolbar.addWidget(self.combo_width)
        toolbar.addSeparator()
        
        op_label = QLabel(" OP: ")
        op_label.setStyleSheet("color: #8ab4ff; font-family: 'Courier New'; font-weight: bold;")
        toolbar.addWidget(op_label)
        self.combo_op = QComboBox()
        self.combo_op.addItems([
            'ADD', 'SUB', 'INC', 'DEC', 'ABS',
            'AND', 'OR', 'XOR', 'NAND', 'NOR', 'XNOR', 'NOT',
            'MUX', 'CMP', 'MIN', 'MAX',
            'SHL', 'SHR', 'SAR', 'ROL', 'ROR', 'REV', 'POPCNT'
        ])
        toolbar.addWidget(self.combo_op)
        toolbar.addSeparator()
        
        self.btn_pause = QPushButton("▶ PLAY")
        self.btn_pause.setCheckable(True)
        self.btn_pause.setChecked(False)
        toolbar.addWidget(self.btn_pause)
        
        self.btn_step = QPushButton("⏭ STEP")
        self.btn_step.setToolTip("Single clock cycle (S)")
        toolbar.addWidget(self.btn_step)
        
        self.btn_random = QPushButton("🎲 RANDOM")
        toolbar.addWidget(self.btn_random)
        
        toolbar.addSeparator()
        
        # Presets are now width-aware - rebuilt when width changes
        self.preset_buttons = []
        self._rebuild_presets()
        
        toolbar.addSeparator()
        
        flow_label = QLabel(" FLOW: ")
        flow_label.setStyleSheet("color: #8ab4ff; font-family: 'Courier New'; font-weight: bold;")
        toolbar.addWidget(flow_label)
        self.slider_flow = QSlider(Qt.Horizontal)
        self.slider_flow.setRange(1, 10)
        self.slider_flow.setValue(4)
        self.slider_flow.setFixedWidth(120)
        self.slider_flow.setStyleSheet("""
            QSlider::groove:horizontal { background: #1a1f35; height: 4px; border-radius: 2px; }
            QSlider::handle:horizontal { background: #4a6aaa; width: 14px; margin: -5px 0; border-radius: 7px; }
            QSlider::handle:horizontal:hover { background: #6a8acc; }
        """)
        toolbar.addWidget(self.slider_flow)
        
        self.addToolBar(toolbar)

    def _rebuild_presets(self):
        """Rebuild preset buttons for current bit width."""
        for btn in self.preset_buttons:
            btn.setParent(None)
            btn.deleteLater()
        self.preset_buttons.clear()
        
        n = self.visualizer.num_bits
        mask = self.visualizer._mask
        
        # Helper to create alternating bit masks (e.g., 0x5555... and 0xAAAA...)
        def alt_mask(val):
            res = 0
            for i in range(n):
                if (i % 2) == val:
                    res |= (1 << i)
            return res
            
        presets = [
            ("MAX RIPPLE", mask, 1, 'ADD'),
            ("XOR MASK", alt_mask(1), alt_mask(0), 'XOR'),
            ("SHIFT L", 0xF, 0, 'SHL'),
            ("NAND", 0x0F0F0F0F & mask, 0xF0F0F0F0 & mask, 'NAND'),
            ("CMP EQ", 0x12345678 & mask, 0x12345678 & mask, 'CMP'),
            ("BIT REV", self.visualizer._sign_mask | 1, 0, 'REV'),
            ("ABS NEG", mask - 0xFF, 0, 'ABS'),
        ]
        
        toolbar = self.findChild(QToolBar)
        for name, a, b, op in presets:
            btn = QPushButton(name)
            btn.setStyleSheet("background-color: #1a2535;")
            btn.clicked.connect(lambda checked, a=a, b=b, op=op: self._apply_preset(a, b, op))
            toolbar.addWidget(btn)
            self.preset_buttons.append(btn)

    def _build_side_panel(self):
        dock = QDockWidget("Control Panel", self)
        dock.setFeatures(QDockWidget.DockWidgetMovable | QDockWidget.DockWidgetFloatable)
        dock.setStyleSheet("""
            QDockWidget { color: #8ab4ff; }
            QDockWidget::title {
                background-color: #0d1020;
                padding: 8px;
                border-bottom: 1px solid #2a3555;
                text-align: left;
                font-family: 'Courier New';
                font-weight: bold;
            }
        """)
        
        side_widget = QWidget()
        side_widget.setStyleSheet("background-color: #0a0d1a;")
        side_widget.setMinimumWidth(320)
        side_widget.setMaximumWidth(400)
        
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.NoFrame)
        scroll.setStyleSheet("QScrollArea { border: none; background-color: #0a0d1a; }")
        
        container = QWidget()
        container.setStyleSheet("background-color: #0a0d1a;")
        layout = QVBoxLayout(container)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(10)
        
        # --- Bit Width Section ---
        width_box = CollapsibleBox("▸ BIT WIDTH MODE")
        self.width_info = QLabel()
        self.width_info.setStyleSheet("color: #8899bb; font-family: 'Courier New'; font-size: 11px; padding: 4px;")
        self.width_info.setWordWrap(True)
        self._update_width_info()
        width_box.content_layout.addWidget(self.width_info)
        
        width_btns = QHBoxLayout()
        for w in SUPPORTED_WIDTHS:
            btn = QPushButton(f"{w}-BIT")
            btn.setStyleSheet("""
                QPushButton { background-color: #1a2535; padding: 8px; }
                QPushButton:hover { background-color: #2a3555; }
            """)
            btn.clicked.connect(lambda checked, w=w: self._change_bit_width(w))
            width_btns.addWidget(btn)
        width_box.content_layout.addLayout(width_btns)
        layout.addWidget(width_box)
        
        # --- Inputs Section ---
        inputs_box = CollapsibleBox("▸ INPUT REGISTERS")
        form_a = QFormLayout()
        form_a.setLabelAlignment(Qt.AlignRight)
        self.edit_a = QLineEdit()
        self.edit_a.setStyleSheet("""
            QLineEdit {
                background-color: #05070A; color: #00ffff;
                border: 1px solid #2a3555; border-radius: 3px;
                padding: 6px; font-family: 'Courier New';
                font-weight: bold; font-size: 14px;
            }
            QLineEdit:focus { border-color: #00ffff; }
        """)
        form_a.addRow(self._make_label("A (Hex):"), self.edit_a)
        inputs_box.content_layout.addLayout(form_a)
        
        form_b = QFormLayout()
        form_b.setLabelAlignment(Qt.AlignRight)
        self.edit_b = QLineEdit()
        self.edit_b.setStyleSheet(self.edit_a.styleSheet().replace("#00ffff", "#ff00ff"))
        form_b.addRow(self._make_label("B (Hex):"), self.edit_b)
        inputs_box.content_layout.addLayout(form_b)
        
        # Apply Hex Validation to inputs
        hex_regex = QRegularExpression("^[0-9a-fA-F]*$")
        validator = QRegularExpressionValidator(hex_regex)
        self.edit_a.setValidator(validator)
        self.edit_b.setValidator(validator)
        
        # Now that both fields exist, safely update their widths and limits
        self._update_input_field_widths()
        
        self.decimal_label = QLabel()
        self.decimal_label.setStyleSheet("color: #6a8acc; font-family: 'Courier New'; font-size: 10px; padding: 4px;")
        self.decimal_label.setWordWrap(True)
        self._update_decimal_display()
        inputs_box.content_layout.addWidget(self.decimal_label)
        
        hint = QLabel("💡 Click LEDs in the visualization to toggle bits")
        hint.setStyleSheet("color: #8899bb; font-family: 'Courier New'; font-size: 10px; font-style: italic; padding: 4px;")
        hint.setWordWrap(True)
        inputs_box.content_layout.addWidget(hint)
        
        layout.addWidget(inputs_box)
        
        # --- Result Section ---
        result_box = CollapsibleBox("▸ COMPUTED RESULT")
        self.result_hex = QLabel()
        self.result_hex.setStyleSheet("""
            QLabel {
                background-color: #05070A; color: #b4ffca;
                border: 1px solid #2a5535; border-radius: 3px;
                padding: 10px; font-family: 'Courier New';
                font-weight: bold; font-size: 16px;
            }
        """)
        self.result_hex.setWordWrap(True)
        result_box.content_layout.addWidget(self.result_hex)
        
        self.result_bin = QLabel()
        self.result_bin.setWordWrap(True)
        self.result_bin.setStyleSheet("color: #6a8acc; font-family: 'Courier New'; font-size: 10px; padding: 4px;")
        result_box.content_layout.addWidget(self.result_bin)
        
        self.result_signed = QLabel()
        self.result_signed.setWordWrap(True)
        self.result_signed.setStyleSheet("color: #8ab4ff; font-family: 'Courier New'; font-size: 11px; padding: 4px;")
        result_box.content_layout.addWidget(self.result_signed)
        
        layout.addWidget(result_box)
        
        # --- Flags Section ---
        flags_box = CollapsibleBox("▸ STATUS FLAGS")
        self.flags_display = QLabel()
        self.flags_display.setStyleSheet("""
            QLabel {
                background-color: #05070A;
                border: 1px solid #2a3555;
                border-radius: 3px;
                padding: 10px;
                font-family: 'Courier New';
                font-size: 11px;
            }
        """)
        self.flags_display.setTextFormat(Qt.RichText)
        flags_box.content_layout.addWidget(self.flags_display)
        self._update_flags_display()
        layout.addWidget(flags_box)
        
        # --- Keyboard Shortcuts ---
        keys_box = CollapsibleBox("▸ KEYBOARD SHORTCUTS")
        keys_text = QLabel(
            "<span style='color:#0ff'>SPACE</span> — Pause / Resume<br>"
            "<span style='color:#0ff'>S</span> — Single step<br>"
            "<span style='color:#0ff'>R</span> — Randomize inputs<br>"
            "<span style='color:#0ff'>←/→</span> — Shift Right / Left<br>"
            "<span style='color:#0ff'>Click</span> — Toggle bits on LEDs"
        )
        keys_text.setStyleSheet("color: #8899bb; font-family: 'Courier New'; font-size: 11px; padding: 4px;")
        keys_text.setTextFormat(Qt.RichText)
        keys_box.content_layout.addWidget(keys_text)
        layout.addWidget(keys_box)
        
        # --- Info Section ---
        info_box = CollapsibleBox("▸ ABOUT")
        info_text = QLabel(
            "Multi-width ALU waterfall (16/32/64/128-bit) with 23 operations.<br><br>"
            "<b>Width Modes:</b><br>"
            "• <span style='color:#0ff'>16-bit</span> — Classic microcontroller (8086, AVR)<br>"
            "• <span style='color:#0ff'>32-bit</span> — Standard RISC/CISC (ARM, x86)<br>"
            "• <span style='color:#0ff'>64-bit</span> — Modern processors (x86-64)<br>"
            "• <span style='color:#0ff'>128-bit</span> — SIMD/vector registers (SSE, NEON)<br><br>"
            "At 64/128-bit, gates switch to compact symbol mode for performance."
        )
        info_text.setWordWrap(True)
        info_text.setStyleSheet("color: #8899bb; font-family: 'Courier New'; font-size: 11px; padding: 4px;")
        info_text.setTextFormat(Qt.RichText)
        info_box.content_layout.addWidget(info_text)
        layout.addWidget(info_box)
        
        layout.addStretch()
        
        scroll.setWidget(container)
        # FIX: Set widget directly on dock instead of creating a new layout
        dock.setWidget(scroll)
        
        self.addDockWidget(Qt.RightDockWidgetArea, dock)

    def _make_label(self, text):
        lbl = QLabel(text)
        lbl.setStyleSheet("color: #8ab4ff; font-family: 'Courier New'; font-weight: bold;")
        return lbl

    def _make_separator(self):
        # FIX: Add styled separator frame for QStatusBar
        sep = QFrame()
        sep.setFrameShape(QFrame.VLine)
        sep.setStyleSheet("background-color: #2a3555; max-width: 1px; margin: 0px 4px;")
        return sep

    def _build_status_bar(self):
        self.status_bar = QStatusBar()
        self.status_bar.setStyleSheet("""
            QStatusBar {
                background-color: #0d1020; color: #8ab4ff;
                border-top: 1px solid #2a3555;
                font-family: 'Courier New'; font-size: 11px;
                padding: 2px 8px;
            }
            QStatusBar::item { border: none; }
        """)
        self.setStatusBar(self.status_bar)
        
        self.status_width = QLabel("WIDTH: 32-bit")
        self.status_width.setStyleSheet("color: #0ff; font-weight: bold;")
        self.status_particles = QLabel("Particles: 0")
        self.status_slices = QLabel("Slices: 32")
        self.status_fps = QLabel("FPS: 60.0")
        self.status_op = QLabel("OP: ADD")
        self.status_state = QLabel("● RUNNING")
        self.status_state.setStyleSheet("color: #00ff88;")
        self.status_flags = QLabel("Z:0 C:0 V:0 N:0 P:0")
        self.status_flags.setStyleSheet("color: #ffc864;")
        
        self.status_bar.addWidget(self.status_state)
        # FIX: Replaced .addSeparator() with .addWidget(self._make_separator())
        self.status_bar.addWidget(self._make_separator())
        self.status_bar.addWidget(self.status_width)
        self.status_bar.addWidget(self._make_separator())
        self.status_bar.addWidget(self.status_op)
        self.status_bar.addWidget(self._make_separator())
        self.status_bar.addWidget(self.status_flags)
        self.status_bar.addWidget(self._make_separator())
        self.status_bar.addWidget(self.status_particles)
        self.status_bar.addWidget(self._make_separator())
        self.status_bar.addWidget(self.status_slices)
        self.status_bar.addPermanentWidget(self.status_fps)
        
        self.visualizer.stats_updated.connect(self._update_stats)

    def _update_stats(self, particles, slices, fps, flags, width):
        self.status_particles.setText(f"Particles: {particles}")
        self.status_slices.setText(f"Slices: {slices}")
        self.status_fps.setText(f"FPS: {fps:.1f}")
        self.status_flags.setText(f"Z:{flags['Z']} C:{flags['C']} V:{flags['V']} N:{flags['N']} P:{flags['P']}")
        self.status_width.setText(f"WIDTH: {width}-bit")
        self._update_flags_display()

    def _update_width_info(self):
        n = self.visualizer.num_bits
        descriptions = {
            16: "16-bit mode — Classic microcontroller width. Used in 8086, AVR, and many embedded systems. Gates are large and detailed.",
            32: "32-bit mode — Standard processor width. Used in ARM, MIPS, and 32-bit x86. The default visualization.",
            64: "64-bit mode — Modern processor width. Used in x86-64 and ARM64. Gates are half the size of 32-bit mode.",
            128: "128-bit mode — SIMD/vector width. Used in SSE, NEON, and GPU registers. Gates use compact symbol mode for performance."
        }
        self.width_info.setText(
            f"<b>Current: {n}-bit</b><br>"
            f"Hex digits: {n // 4}<br>"
            f"Max value: 0x{self.visualizer._mask:X}<br><br>"
            f"{descriptions.get(n, '')}"
        )

    def _update_input_field_widths(self):
        """Adjust input field max length based on bit width."""
        hex_chars = self.visualizer.num_bits // 4
        self.edit_a.setMaxLength(hex_chars)
        self.edit_b.setMaxLength(hex_chars)
        # Set fixed width based on content
        char_width = 9 * hex_chars + 20
        self.edit_a.setFixedWidth(max(120, char_width))
        self.edit_b.setFixedWidth(max(120, char_width))
        # Update text
        self.edit_a.setText(f"{self.visualizer.val_a:0{hex_chars}X}")
        self.edit_b.setText(f"{self.visualizer.val_b:0{hex_chars}X}")

    def _sync_input_fields(self):
        """Sync the side panel text fields when inputs are changed via clicking LEDs."""
        hex_chars = self.visualizer.num_bits // 4
        a_text = f"{self.visualizer.val_a:0{hex_chars}X}"
        b_text = f"{self.visualizer.val_b:0{hex_chars}X}"
        
        # Block signals to prevent textChanged from recursively re-parsing the inputs
        self.edit_a.blockSignals(True)
        self.edit_b.blockSignals(True)
        self.edit_a.setText(a_text)
        self.edit_b.setText(b_text)
        self.edit_a.blockSignals(False)
        self.edit_b.blockSignals(False)
        
        self._update_decimal_display()
        self._update_result_display()

    def _update_flags_display(self):
        f = self.visualizer.flags
        def led(name, val, color):
            if val:
                return f"<span style='color:{color}; font-weight:bold;'>● {name}</span>"
            return f"<span style='color:#444;'>○ {name}</span>"
        
        self.flags_display.setText(
            f"{led('Z', f['Z'], '#64c8ff')} &nbsp; "
            f"{led('C', f['C'], '#ffc864')} &nbsp; "
            f"{led('V', f['V'], '#ff6496')} &nbsp; "
            f"{led('N', f['N'], '#c864ff')} &nbsp; "
            f"{led('P', f['P'], '#64ffc8')}<br>"
            f"<span style='color:#6a8acc; font-size:10px;'>"
            f"Zero | Carry | Overflow | Negative | Parity</span>"
        )

    def _update_decimal_display(self):
        try:
            a = self.visualizer.val_a
            b = self.visualizer.val_b
            a_signed = self.visualizer._to_signed(a)
            b_signed = self.visualizer._to_signed(b)
            self.decimal_label.setText(
                f"A (dec): {a_signed:,}<br>B (dec): {b_signed:,}"
            )
        except Exception:
            pass

    def _update_result_display(self):
        res = self.visualizer._compute_result()
        res_signed = self.visualizer._to_signed(res)
        hex_chars = self.visualizer.num_bits // 4
        self.result_hex.setText(f"0x{res:0{hex_chars}X}")
        
        # For 128-bit, binary is too long to display nicely
        if self.visualizer.num_bits <= 64:
            self.result_bin.setText(f"BIN: {res:0{self.visualizer.num_bits}b}")
        else:
            # Show in 32-bit chunks
            chunks = []
            for i in range(self.visualizer.num_bits // 32 - 1, -1, -1):
                chunk = (res >> (i * 32)) & 0xFFFFFFFF
                chunks.append(f"{chunk:08b}")
            self.result_bin.setText("BIN: " + " ".join(chunks))
        
        if self.visualizer.operation == 'POPCNT':
            self.result_signed.setText(f"Population Count: {res} bits set")
        else:
            self.result_signed.setText(f"Signed: {res_signed:,}<br>Unsigned: {res:,}")

    def _apply_theme(self):
        self.setStyleSheet("""
            QMainWindow { background-color: #05070A; }
            QScrollBar:vertical {
                background: #0a0d1a; width: 10px; border: none;
            }
            QScrollBar::handle:vertical {
                background: #2a3555; border-radius: 5px; min-height: 20px;
            }
            QScrollBar::handle:vertical:hover { background: #4a6aaa; }
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0px; }
        """)

    def _connect_signals(self):
        self.edit_a.textChanged.connect(self._update_inputs)
        self.edit_b.textChanged.connect(self._update_inputs)
        self.combo_op.currentTextChanged.connect(self._update_operation)
        self.combo_width.currentTextChanged.connect(self._on_width_combo_changed)
        self.slider_flow.valueChanged.connect(lambda v: setattr(self.visualizer, 'flow_rate', v))
        self.btn_random.clicked.connect(self._randomize)
        self.btn_pause.toggled.connect(self._toggle_pause)
        self.btn_step.clicked.connect(self._step_once)
        self.visualizer.bit_width_changed.connect(self._on_bit_width_changed)
        self.visualizer.input_changed.connect(self._sync_input_fields)

    def _on_width_combo_changed(self, text):
        try:
            n = int(text)
            if n in SUPPORTED_WIDTHS:
                self._change_bit_width(n)
        except ValueError:
            pass

    def _on_bit_width_changed(self, n):
        """Called when bit width changes - update all UI elements."""
        self.combo_width.setCurrentText(str(n))
        self._update_input_field_widths()
        self._update_decimal_display()
        self._update_result_display()
        self._update_width_info()
        self._rebuild_presets()
        self.status_width.setText(f"WIDTH: {n}-bit")
        self.setWindowTitle(f"{n}-Bit ALU Waterfall Visualizer — Ultimate Edition")

    def _change_bit_width(self, n):
        """Change the bit width from any source."""
        self.visualizer.set_bit_width(n)

    def _update_inputs(self):
        try:
            hex_chars = self.visualizer.num_bits // 4
            a_str = self.edit_a.text().replace(' ', '').replace('0x', '').replace('0X', '')
            b_str = self.edit_b.text().replace(' ', '').replace('0x', '').replace('0X', '')
            if a_str:
                self.visualizer.val_a = int(a_str, 16) & self.visualizer._mask
            if b_str:
                self.visualizer.val_b = int(b_str, 16) & self.visualizer._mask
            self._update_decimal_display()
            self._update_result_display()
        except ValueError:
            pass

    def _update_operation(self, op):
        self.visualizer.operation = op
        self.status_op.setText(f"OP: {op}")
        self._update_result_display()

    def _randomize(self):
        self.visualizer.val_a = random.randint(0, self.visualizer._mask)
        self.visualizer.val_b = random.randint(0, self.visualizer._mask)
        hex_chars = self.visualizer.num_bits // 4
        self.edit_a.setText(f"{self.visualizer.val_a:0{hex_chars}X}")
        self.edit_b.setText(f"{self.visualizer.val_b:0{hex_chars}X}")
        self._update_decimal_display()
        self._update_result_display()

    def _apply_preset(self, a, b, op):
        self.visualizer.val_a = a & self.visualizer._mask
        self.visualizer.val_b = b & self.visualizer._mask
        self.visualizer.operation = op
        hex_chars = self.visualizer.num_bits // 4
        self.edit_a.setText(f"{self.visualizer.val_a:0{hex_chars}X}")
        self.edit_b.setText(f"{self.visualizer.val_b:0{hex_chars}X}")
        self.combo_op.setCurrentText(op)
        self._update_decimal_display()
        self._update_result_display()

    def _toggle_pause(self, checked):
        self.visualizer.paused = not checked
        self.btn_pause.setText("❚❚ PAUSE" if not self.visualizer.paused else "▶ PLAY")
        if self.visualizer.paused:
            self.status_state.setText("● PAUSED")
            self.status_state.setStyleSheet("color: #ff8800;")
        else:
            self.status_state.setText("● RUNNING")
            self.status_state.setStyleSheet("color: #00ff88;")

    def _step_once(self):
        self.visualizer.paused = True
        self.visualizer.step_pending = True
        self.btn_pause.setChecked(True)
        self.btn_pause.setText("▶ PLAY")
        self.status_state.setText("● STEP")
        self.status_state.setStyleSheet("color: #ffcc00;")


if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    
    palette = QPalette()
    palette.setColor(QPalette.Window, QColor(10, 13, 26))
    palette.setColor(QPalette.WindowText, QColor(200, 220, 255))
    palette.setColor(QPalette.Base, QColor(5, 7, 10))
    palette.setColor(QPalette.Text, QColor(200, 220, 255))
    palette.setColor(QPalette.Button, QColor(26, 31, 53))
    palette.setColor(QPalette.ButtonText, QColor(200, 220, 255))
    app.setPalette(palette)
    
    window = ALUWaterfall()
    window.show()
    sys.exit(app.exec())