#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
WATERGATE 3 — Canal Lock Computer (Compute Lab Edition)
=======================================================
16 / 32 / 64 / 128-bit canal computer. Every pound is a bit:
water = 1, dry = 0. Gates lift as waves sweep the flight;
ADD/SUB ripple carry pound-by-pound; overflow spills the tower.

New in v3
---------
* ⌨ Keyboard bit editing: click a canal, then arrows + Space/Enter
* 🧮 Expression evaluator ("Compute" box):  (A<<4)|0xF, gcd(A,B), popcount(A)…
* ✖️➗ MUL / DIV / MOD-style ops; DIV → A=quotient, B=remainder
* 🧰 Bit toolbox: REV, BSWAP, POP, CLZ, CTZ, INC, DEC, ABS
* 📜 Compute log — every result is recorded with a step number
* 🔤 Text mode: pour ASCII strings into a canal, read them back out
* 📚 9 documented example programs (GCD, shift-add multiply, Collatz,
  Gray code, countdown, …) with descriptions and ▶ Load & Run
* 🧠 Extended CPU ISA: SWP, MUL, INC/DEC, register-arg shifts,
  JL / JGE jump aliases
* Fixes v2's startup crash (bad QCheckBox construction)

Requires:  pip install PySide6
Run:       python watergate.py
"""

import ast
import math
import random
import re
import sys

from PySide6.QtCore import Qt, QElapsedTimer, QPointF, QRectF, QTimer, QSettings, Signal
from PySide6.QtGui import (QColor, QFont, QKeySequence, QPainter, QPainterPath,
                           QPen, QShortcut, QTextCursor, QTextFormat)
from PySide6.QtWidgets import (
    QApplication, QButtonGroup, QCheckBox, QComboBox, QDialog, QFileDialog,
    QFrame, QGridLayout, QGroupBox, QHBoxLayout, QLabel, QLineEdit, QMainWindow,
    QPlainTextEdit, QPushButton, QScrollArea, QSlider, QSpinBox, QTextBrowser,
    QTextEdit, QVBoxLayout, QWidget,
)

CELL_FILL_TIME = 0.12
MEM_SLOTS = 16
LOG_LIMIT = 400

STYLESHEET = """
QWidget { background: #0d1218; color: #cfd8e3;
          font-family: 'Segoe UI','Noto Sans',sans-serif; font-size: 13px; }
QLabel  { background: transparent; }
QGroupBox { background: transparent; border: 1px solid #26313e; border-radius: 8px;
            margin-top: 11px; padding: 6px; font-weight: 600; }
QGroupBox::title { subcontrol-origin: margin; left: 10px; padding: 0 4px; color: #7fd0ff; }
QLineEdit { background: #10161e; border: 1px solid #2a3542; border-radius: 5px;
            padding: 4px 7px; color: #e8f1fa;
            font-family: 'Consolas','DejaVu Sans Mono',monospace; }
QLineEdit:read-only { color: #9fb6cc; background: #0f151d; }
QPlainTextEdit { background: #10161e; border: 1px solid #2a3542; border-radius: 5px;
                 padding: 4px; color: #e8f1fa;
                 font-family: 'Consolas','DejaVu Sans Mono',monospace;
                 font-size: 12px; }
QPlainTextEdit:read-only { color: #9fb6cc; background: #0e141b; }
QSpinBox { background: #10161e; border: 1px solid #2a3542; border-radius: 5px;
           padding: 2px 5px; color: #e8f1fa; }
QComboBox { background: #10161e; border: 1px solid #2a3542; border-radius: 5px;
            padding: 3px 8px; color: #dfe9f4; }
QComboBox:hover { border-color: #3f8cc9; }
QComboBox QAbstractItemView { background: #10161e; color: #dfe9f4;
                              selection-background-color: #1d4d6e; }
QCheckBox { spacing: 6px; }
QCheckBox::indicator { width: 15px; height: 15px; border-radius: 3px;
                       border: 1px solid #2c3946; background: #10161e; }
QCheckBox::indicator:checked { background: #57b0ff; border-color: #7fd0ff; }
QPushButton { background: #16202b; border: 1px solid #2c3946; border-radius: 5px;
              padding: 5px 8px; color: #d9e7f5; }
QPushButton:hover  { background: #1c2c3d; border-color: #3f8cc9; color: #fff; }
QPushButton:pressed{ background: #14304e; }
QPushButton:checked{ background: #1d4d6e; border-color: #57b0ff; color: #fff; }
QPushButton:disabled { color: #5a6875; border-color: #232c37; background: #121821; }
QSlider::groove:horizontal { height: 4px; background: #24303d; border-radius: 2px; }
QSlider::handle:horizontal { width: 13px; margin: -5px 0; border-radius: 6px;
                             background: #4aa3e0; }
QStatusBar { background: #0a0e13; border-top: 1px solid #1c2530; }
QStatusBar QLabel { color: #8fa3b8; background: transparent; }
QScrollArea { border: none; background: transparent; }
QScrollBar:vertical { background: #0d1218; width: 9px; }
QScrollBar::handle:vertical { background: #2a3542; border-radius: 4px; min-height: 30px; }
QScrollBar::add-line, QScrollBar::sub-line { height: 0; }
QToolTip { background: #10161e; color: #cfe6ff; border: 1px solid #3f8cc9; }
"""


# ---------------------------------------------------------------- model bits
class Cell:
    __slots__ = ("level", "target")

    def __init__(self, level=0.0, target=0.0):
        self.level = level
        self.target = target


class CanalRow:
    def __init__(self, name, color_hex, n):
        self.name = name
        self.color_hex = color_hex
        self.value = 0
        self.rebuild(n)

    def rebuild(self, n):
        self.n = n
        self.value &= (1 << n) - 1
        self.cells = []
        for i in range(n):
            b = float((self.value >> (n - 1 - i)) & 1)
            self.cells.append(Cell(b, b))
        self.gates = [0.0] * (n + 1)
        self.tower = 0.15
        self.flow = None


class FlagLamp(QWidget):
    def __init__(self, text, color_hex, parent=None):
        super().__init__(parent)
        self._text = text
        self._color = QColor(color_hex)
        self._on = False
        self.setMinimumSize(72, 30)

    def set_on(self, on):
        on = bool(on)
        if on != self._on:
            self._on = on
            self.update()

    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        d = QRectF(4, 8, 14, 14)
        if self._on:
            glow = QColor(self._color)
            glow.setAlpha(70)
            p.setPen(Qt.NoPen)
            p.setBrush(glow)
            p.drawEllipse(d.adjusted(-5, -5, 5, 5))
        p.setBrush(QColor(self._color) if self._on else QColor("#1c242e"))
        p.setPen(QPen(self._color if self._on else QColor("#3a4654"), 1.4))
        p.drawEllipse(d)
        p.setPen(self._color if self._on else QColor("#5d6c7d"))
        p.setFont(QFont("Segoe UI", 8, QFont.Bold))
        p.drawText(QRectF(24, 0, self.width() - 24, 30),
                   Qt.AlignVCenter | Qt.AlignLeft, self._text)


# ------------------------------------------------------------- canal display
class CanalWidget(QWidget):
    bitsEdited = Signal(str)
    beginEdit = Signal()
    editRowChanged = Signal(str)

    ROW_DEFS = (("A", "#3fb6ff"), ("B", "#ffb054"), ("OUT", "#57e389"))

    def __init__(self, parent=None):
        super().__init__(parent)
        self.n = 16
        self.mask = (1 << 16) - 1
        self.rows = {name: CanalRow(name, col, 16) for name, col in self.ROW_DEFS}
        self.edit_row = "A"
        self.locked_row = None
        self.speed_mult = 1.0
        self.phase = 0.0
        self.carry = False
        self.hover = None
        self.cursor_idx = None          # keyboard cursor (display index)
        self.focus_idx = None
        self.pulses = []

        self.setMinimumSize(680, 350)
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.StrongFocus)

        self._clock = QTimer(self)
        self._clock.timeout.connect(self._tick)
        self._clock.start(16)
        self._elapsed = QElapsedTimer()
        self._elapsed.start()

    # ------------------------------------------------------------- geometry
    def _geom(self):
        w, h = self.width(), self.height()
        mleft, mright = 64.0, 16.0
        top = 8.0 + 18.0
        rh, gap = 88.0, 16.0
        y0 = top + max(0.0, (h - top - 10.0 - (3 * rh + 2 * gap)) / 2.0)
        cw = (w - mleft - mright) / self.n
        return mleft, y0, cw, rh, gap

    # ------------------------------------------------------------ animation
    def _tick(self):
        dt = min(0.05, self._elapsed.restart() / 1000.0)
        self.phase += dt
        n = self.n

        for pl in self.pulses:
            pl["t"] += dt * 1.6
        self.pulses = [pl for pl in self.pulses if pl["t"] < 1.0]

        for row in self.rows.values():
            tower_target = 1.0 if row.flow is not None else 0.15
            row.tower += (tower_target - row.tower) * min(1.0, dt * 3.0)

            f = row.flow
            if f is not None:
                f["front"] += (n / 1.4) * self.speed_mult * dt
                front = f["front"]
                for i in range(n + 1):
                    row.gates[i] = max(0.0, 1.0 - abs(front - i) / 1.2)
                for i in range(n):
                    if front >= i + 0.35:
                        row.cells[i].target = f["bits"][i]
                if front > n + 2.0:
                    settled = True
                    for i, c in enumerate(row.cells):
                        c.target = f["bits"][i]
                        if abs(c.level - c.target) > 0.004:
                            settled = False
                    if settled:
                        for c in row.cells:
                            c.level = c.target
                        row.gates = [0.0] * (n + 1)
                        row.flow = None
            else:
                decay = dt * 2.5
                for i in range(n + 1):
                    if row.gates[i] > 0.0:
                        row.gates[i] = max(0.0, row.gates[i] - decay)

            rate = dt / CELL_FILL_TIME
            for c in row.cells:
                if c.level < c.target:
                    c.level = min(c.target, c.level + rate)
                elif c.level > c.target:
                    c.level = max(c.target, c.level - rate)

        self.update()

    # ------------------------------------------------------------ public API
    def set_value(self, name, value, flow=True):
        row = self.rows[name]
        v = value & self.mask
        row.value = v
        n = self.n
        if flow:
            bits = [float((v >> (n - 1 - i)) & 1) for i in range(n)]
            row.flow = {"front": -1.5, "bits": bits}
        else:
            row.flow = None
            for i in range(n):
                row.cells[i].target = float((v >> (n - 1 - i)) & 1)
        self.update()

    def poke_bit(self, name, p, val, wiggle=True):
        row = self.rows[name]
        val = 1 if val else 0
        row.value = (row.value & ~(1 << p)) | (val << p)
        idx = self.n - 1 - p
        row.cells[idx].target = float(val)
        if row.flow is not None:
            row.flow["bits"][idx] = float(val)
        if wiggle:
            row.gates[idx] = max(row.gates[idx], 0.6)
            row.gates[idx + 1] = max(row.gates[idx + 1], 0.6)
        self.update()

    def set_word_size(self, n):
        self.n = n
        self.mask = (1 << n) - 1
        for row in self.rows.values():
            row.rebuild(n)
        self.pulses = []
        self.focus_idx = None
        self.hover = None
        self.cursor_idx = None
        self.setMinimumWidth(70 + n * 6)
        self.update()

    def set_edit_row(self, name):
        if name != self.edit_row:
            self.edit_row = name
            self.update()
            self.editRowChanged.emit(name)

    def cycle_edit_row(self, delta):
        names = [r[0] for r in self.ROW_DEFS]
        i = (names.index(self.edit_row) + delta) % len(names)
        self.set_edit_row(names[i])

    def set_locked(self, name):
        self.locked_row = name

    def set_speed(self, mult):
        self.speed_mult = mult

    def set_focus(self, idx):
        if idx != self.focus_idx:
            self.focus_idx = idx
            self.update()

    def add_pulse(self, gate_idx):
        for pl in self.pulses:
            if pl["g"] == gate_idx:
                pl["t"] = 0.0
                return
        self.pulses.append({"g": gate_idx, "t": 0.0})

    # --------------------------------------------------------------- editing
    def _toggle_at(self, name, idx):
        self.beginEdit.emit()                      # undo snapshot FIRST
        row = self.rows[name]
        pbit = self.n - 1 - idx
        row.value ^= 1 << pbit
        b = float((row.value >> pbit) & 1)
        row.cells[idx].target = b
        if row.flow is not None:
            row.flow["bits"][idx] = b
        row.gates[idx] = max(row.gates[idx], 0.7)
        row.gates[idx + 1] = max(row.gates[idx + 1], 0.7)
        self.bitsEdited.emit(name)

    # --------------------------------------------------------------- mouse
    def mousePressEvent(self, ev):
        ev.accept()
        pos = ev.position()
        mleft, y0, cw, rh, gap = self._geom()
        if pos.x() < mleft - 4:
            return
        idx = int((pos.x() - mleft) / cw)
        if not (0 <= idx < self.n):
            return
        row_index = None
        for k in range(3):
            yy = y0 + k * (rh + gap)
            if yy - 4 <= pos.y() <= yy + rh + 4:
                row_index = k
                break
        if row_index is None:
            return
        name = self.ROW_DEFS[row_index][0]
        if self.locked_row == name:
            return
        self.setFocus()
        self.cursor_idx = idx
        self._toggle_at(name, idx)
        self.update()

    def mouseMoveEvent(self, ev):
        pos = ev.position()
        mleft, y0, cw, rh, gap = self._geom()
        hover = None
        if pos.x() >= mleft - 2:
            idx = int((pos.x() - mleft) / cw)
            if 0 <= idx < self.n:
                for k in range(3):
                    yy = y0 + k * (rh + gap)
                    if yy - 6 <= pos.y() <= yy + rh + 6:
                        hover = (self.ROW_DEFS[k][0], idx)
                        break
        if hover != self.hover:
            self.hover = hover
            self.update()
        self.setCursor(Qt.PointingHandCursor if hover else Qt.ArrowCursor)

    def leaveEvent(self, ev):
        if self.hover:
            self.hover = None
            self.update()
        self.setCursor(Qt.ArrowCursor)

    # ------------------------------------------------------------ keyboard
    def keyPressEvent(self, ev):
        k = ev.key()
        keys = (Qt.Key_Left, Qt.Key_Right, Qt.Key_Up, Qt.Key_Down,
                Qt.Key_Space, Qt.Key_Return, Qt.Key_Enter)
        if k not in keys:
            super().keyPressEvent(ev)
            return
        ev.accept()
        if k in (Qt.Key_Up, Qt.Key_Down):
            self.cycle_edit_row(1 if k == Qt.Key_Down else -1)
            return
        if self.cursor_idx is None:
            self.cursor_idx = 0
            self.update()
            return
        if k == Qt.Key_Left:
            self.cursor_idx = (self.cursor_idx - 1) % self.n
        elif k == Qt.Key_Right:
            self.cursor_idx = (self.cursor_idx + 1) % self.n
        else:
            if self.locked_row != self.edit_row:
                self._toggle_at(self.edit_row, self.cursor_idx)
        self.update()

    # -------------------------------------------------------------- painting
    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.setRenderHint(QPainter.TextAntialiasing, True)

        bg = QLinearGradient(0, 0, 0, self.height())
        bg.setColorAt(0.0, QColor("#0e141c"))
        bg.setColorAt(1.0, QColor("#090d12"))
        p.fillRect(self.rect(), bg)

        mleft, y0, cw, rh, gap = self._geom()
        n = self.n
        x0, x1 = mleft, mleft + cw * n

        self._draw_ruler(p, x0, y0 - 10.0, cw, n)
        for k, (name, col) in enumerate(self.ROW_DEFS):
            yy = y0 + k * (rh + gap)
            self._draw_row(p, self.rows[name], x0, x1, yy, rh, cw,
                           name, col, name == self.edit_row)

        # ripple-adder focus band
        if self.focus_idx is not None:
            fx = x0 + self.focus_idx * cw
            p.setPen(QPen(QColor(150, 215, 255, 150), 1))
            p.setBrush(QColor(140, 205, 255, 34))
            for k in range(3):
                yy = y0 + k * (rh + gap)
                p.drawRect(QRectF(fx + 0.5, yy + 0.5, cw - 1, rh - 1))

        # carry droplets hopping over OUT gates
        yy_out = y0 + 2 * (rh + gap)
        for pl in self.pulses:
            t = pl["t"]
            gx = x0 + pl["g"] * cw
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(185, 235, 255, int(235 * (1 - t))))
            py = yy_out + 1 - 15 * math.sin(math.pi * t)
            p.drawEllipse(QPointF(gx, py), 2.4, 3.0)
            p.setPen(QPen(QColor(140, 215, 255, int(150 * (1 - t))), 1))
            p.setBrush(Qt.NoBrush)
            rr = 5 + 5 * t
            p.drawEllipse(QPointF(gx, yy_out), rr, rr)

        # keyboard cursor: dashed box on the edit row
        if self.cursor_idx is not None:
            k = [r[0] for r in self.ROW_DEFS].index(self.edit_row)
            yy = y0 + k * (rh + gap)
            pen = QPen(QColor("#eaf6ff"), 1.6, Qt.DashLine)
            p.setPen(pen)
            p.setBrush(Qt.NoBrush)
            p.drawRect(QRectF(x0 + self.cursor_idx * cw + 0.5, yy + 0.5,
                              cw - 1, rh - 1))

        # hover inspection
        if self.hover:
            name, idx = self.hover
            row = self.rows[name]
            pw = n - 1 - idx
            bit = int((row.value >> pw) & 1)
            k = [r[0] for r in self.ROW_DEFS].index(name)
            yy = y0 + k * (rh + gap)
            p.setPen(QPen(QColor("#8fd6ff"), 1.5))
            p.setBrush(Qt.NoBrush)
            p.drawRect(QRectF(x0 + idx * cw + 0.5, yy + 0.5, cw - 1, rh - 1))
            txt = f"{name} · bit {pw} = {bit}   (w={1 << pw})"
            p.setFont(QFont("Consolas", 8))
            twd = p.fontMetrics().horizontalAdvance(txt) + 16
            bx = self.width() - twd - 8
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(13, 20, 30, 235))
            p.drawRoundedRect(QRectF(bx, 4, twd, 20), 4, 4)
            p.setPen(QColor("#9fd8ff"))
            p.drawText(QRectF(bx + 8, 4, twd - 16, 20),
                       Qt.AlignVCenter | Qt.AlignLeft, txt)
        p.end()

    def _draw_ruler(self, p, x0, yr, cw, n):
        font = QFont("Consolas")
        font.setPointSizeF(7.5)
        p.setFont(font)
        for d in range(0, n + 1, 4):
            x = x0 + d * cw
            if d % 8 == 0 and d < n:
                p.setPen(QPen(QColor("#445263"), 1))
                p.drawLine(QPointF(x, yr + 2), QPointF(x, yr + 10))
                p.setPen(QColor("#8fa3b8"))
                label = f"bit {n - 1 - d}" if cw * 8 >= 64 else str(n - 1 - d)
                p.drawText(QRectF(x + 2, yr - 12, 70, 12),
                           Qt.AlignLeft | Qt.AlignVCenter, label)
            elif d < n:
                p.setPen(QPen(QColor("#2c3642"), 1))
                p.drawLine(QPointF(x, yr + 4), QPointF(x, yr + 10))
        p.setPen(QPen(QColor("#445263"), 1))
        p.drawLine(QPointF(x0 + n * cw, yr + 2), QPointF(x0 + n * cw, yr + 10))
        p.setPen(QColor("#54636f"))
        p.drawText(QRectF(x0 + cw * n - 64, yr - 12, 64, 12),
                   Qt.AlignRight | Qt.AlignVCenter, "flow →")

    def _draw_row(self, p, row, x0, x1, y, rh, cw, name, col_hex, is_edit):
        n = row.n
        w_canal = cw * n
        phase = self.phase

        p.setPen(Qt.NoPen)
        p.setBrush(QColor("#0d1219"))
        p.drawRoundedRect(QRectF(x0 - 10, y - 10, w_canal + 20, rh + 20), 6, 6)

        for g in range((n + 3) // 4):
            bx = x0 + g * 4 * cw
            bw = min(4, n - g * 4) * cw
            p.setBrush(QColor("#10161f") if g % 2 == 0 else QColor("#151d29"))
            p.drawRect(QRectF(bx, y, bw, rh))

        for i, c in enumerate(row.cells):
            if c.level > 0.015:
                self._draw_water(p, x0 + i * cw, y, cw, rh, c.level, phase, i)

        p.setBrush(Qt.NoBrush)
        p.setPen(QPen(QColor("#2b3542"), 1))
        p.drawRect(QRectF(x0 + 0.5, y + 0.5, w_canal - 1, rh - 1))
        if cw >= 3:
            p.setPen(QPen(QColor("#232c37"), 1))
            for i in range(1, n):
                xx = x0 + i * cw
                p.drawLine(QPointF(xx, y + 2), QPointF(xx, y + rh - 2))

        p.setPen(Qt.NoPen)
        p.setBrush(QColor("#415062"))
        p.drawRect(QRectF(x0, y, w_canal, 3))
        p.drawRect(QRectF(x0, y + rh - 3, w_canal, 3))

        gw = max(2.0, min(4.0, cw * 0.45))
        for i in range(n + 1):
            gx = x0 + i * cw - gw / 2.0
            o = row.gates[i]
            gh = (rh - 6.0) * (1.0 - o)
            if gh > 0.6:
                grad = QLinearGradient(gx, 0, gx + gw, 0)
                grad.setColorAt(0.0, QColor("#93a1b1"))
                grad.setColorAt(0.5, QColor("#4d5866"))
                grad.setColorAt(1.0, QColor("#93a1b1"))
                p.setPen(QPen(QColor("#1d242d"), 1))
                p.setBrush(grad)
                p.drawRect(QRectF(gx, y + 3, gw, gh))
                if gw >= 3 and gh > 12:
                    p.setPen(QPen(QColor("#39434e"), 1))
                    yy = y + 6
                    while yy < y + 3 + gh - 3:
                        p.drawLine(QPointF(gx + 0.5, yy), QPointF(gx + gw - 0.5, yy))
                        yy += 4.0
            p.setPen(QPen(QColor("#4e5b6c"), 1))
            p.setBrush(QColor("#161d26"))
            p.drawRect(QRectF(gx - 1.5, y - 6, gw + 3, 7))

        f = row.flow
        if f is not None and -1.5 <= f["front"] <= n + 1.5:
            fx = x0 + f["front"] * cw
            glow = QLinearGradient(fx - 7, 0, fx + 7, 0)
            glow.setColorAt(0.0, QColor(140, 225, 255, 0))
            glow.setColorAt(0.5, QColor(140, 225, 255, 80))
            glow.setColorAt(1.0, QColor(140, 225, 255, 0))
            p.setPen(Qt.NoPen)
            p.setBrush(glow)
            p.drawRect(QRectF(fx - 7, y, 14, rh))

        col = QColor(col_hex)
        p.setFont(QFont("Segoe UI", 11, QFont.Bold))
        p.setPen(col if is_edit else col.darker(115))
        p.drawText(QRectF(8, y, 26, rh), Qt.AlignCenter, name)

        tx, tw = 40.0, 15.0
        trect = QRectF(tx, y + 5, tw, rh - 10)
        p.setPen(QPen(QColor("#4a5666"), 1))
        p.setBrush(QColor("#131922"))
        p.drawRoundedRect(trect, 3, 3)
        tl = max(0.0, min(1.0, row.tower))
        if tl > 0.02:
            wy = trect.bottom() - tl * (trect.height() - 2.0)
            grad = QLinearGradient(tx, wy, tx, trect.bottom())
            grad.setColorAt(0.0, QColor(96, 176, 255, 225))
            grad.setColorAt(1.0, QColor(18, 58, 138, 235))
            p.setPen(Qt.NoPen)
            p.setBrush(grad)
            p.drawRect(QRectF(tx + 1.5, wy, tw - 3.0, trect.bottom() - wy))
            p.setPen(QPen(QColor(170, 220, 255, 190), 1))
            p.drawLine(QPointF(tx + 1.5, wy), QPointF(tx + tw - 1.5, wy))
        p.setPen(QPen(QColor("#4a5666"), 2))
        p.drawLine(QPointF(tx + tw, y + 9), QPointF(x0 - 1, y + 9))

        if name == "OUT" and self.carry:
            blink = 0.6 + 0.4 * math.sin(phase * 6.0)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 120, 90, int(90 * blink)))
            p.drawEllipse(QPointF(tx + tw / 2, y + 4), 7, 4)
            for k in range(4):
                t = (phase * 1.5 + k * 0.25) % 1.0
                px = tx + tw + t * 34.0
                py = y + 5 + t * t * 52.0
                if px < x1:
                    p.setBrush(QColor(150, 210, 255, 210))
                    p.drawEllipse(QPointF(px, py), 1.6, 2.4)
            p.setFont(QFont("Segoe UI", 7, QFont.Bold))
            p.setPen(QColor(255, 150, 120, int(200 * blink)))
            p.drawText(QRectF(tx - 6, y - 18, 60, 12),
                       Qt.AlignLeft | Qt.AlignVCenter, "SPILL!")

        if is_edit:
            p.setPen(Qt.NoPen)
            p.setBrush(col)
            p.drawRect(QRectF(x0 - 10, y + rh + 8, w_canal + 20, 2))

    def _draw_water(self, p, cx, y, cw, rh, level, phase, idx):
        top, bot = y + 4.0, y + rh - 4.0
        surf = top + (1.0 - level) * (rh - 8.0)
        amp = min(1.6, cw * 0.22) if cw > 6 else 0.8
        steps = max(2, int(cw / 4) + 1)

        def wave(x):
            return surf + amp * math.sin(phase * 2.6 + x * 0.35 + idx * 1.7)

        path = QPainterPath()
        path.moveTo(cx, bot)
        path.lineTo(cx, surf)
        for s in range(1, steps + 1):
            xx = cx + cw * s / steps
            path.lineTo(xx, wave(xx))
        path.lineTo(cx + cw, bot)
        path.closeSubpath()

        grad = QLinearGradient(cx, surf, cx, bot)
        grad.setColorAt(0.0, QColor(64, 150, 235, 215))
        grad.setColorAt(0.5, QColor(30, 90, 180, 225))
        grad.setColorAt(1.0, QColor(8, 34, 90, 235))
        p.setPen(Qt.NoPen)
        p.setBrush(grad)
        p.drawPath(path)

        p.setPen(QPen(QColor(150, 215, 255, 200), 1.2))
        prev = QPointF(cx, wave(cx))
        for s in range(1, steps + 1):
            xx = cx + cw * s / steps
            cur = QPointF(xx, wave(xx))
            p.drawLine(prev, cur)
            prev = cur

        if level > 0.4 and cw >= 5 and bot - surf - 5 > 4:
            p.setPen(Qt.NoPen)
            for j in range(2):
                t = (phase * 0.35 + j * 0.5 + idx * 0.13) % 1.0
                sx = cx + 1.5 + ((idx * 7 + j * 13) % max(1, int(cw) - 3))
                sy = surf + 3 + t * (bot - surf - 5)
                p.setBrush(QColor(190, 230, 255, int(110 * (1 - t))))
                p.drawEllipse(QPointF(sx, sy), 1.0, 1.0)


# ------------------------------------------------------- safe expression eval
_ALLOWED = (
    ast.Expression, ast.BinOp, ast.UnaryOp, ast.Constant, ast.Name, ast.Load,
    ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod, ast.LShift, ast.RShift,
    ast.BitOr, ast.BitAnd, ast.BitXor, ast.Pow, ast.USub, ast.UAdd, ast.Invert,
    ast.Call,
)


def safe_eval(expr, env):
    """Evaluate an integer expression with a whitelisted AST."""
    tree = ast.parse(expr.strip(), mode="eval")
    for node in ast.walk(tree):
        if not isinstance(node, _ALLOWED):
            raise ValueError(f"not allowed: {type(node).__name__}")
        if isinstance(node, ast.Constant) and not isinstance(node.value, int):
            raise ValueError("only integer constants")
        if isinstance(node, ast.Call):
            if not isinstance(node.func, ast.Name) or node.keywords:
                raise ValueError("bad function call")
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow) and isinstance(node.right, ast.Constant) \
                    and abs(node.right.value) > 64:
                raise ValueError("exponent too large")
            if isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant) \
                    and node.right.value > 4096:
                raise ValueError("shift too large")
    code = compile(tree, "<expr>", "eval")
    raw = int(eval(code, {"__builtins__": {}}, env))   # noqa: S307 (sandboxed)
    if raw.bit_length() > 4096:
        raise ValueError("result too large")
    return raw


# ---------------------------------------------------------------- program DB
# name -> (description, code)
EXAMPLES = {
    "— pick an example —": ("", ""),
    "Count up (loop)": (
        "OUT = 0,1,2,… forever — watch the OUT canal count in water.",
        "; Count 0,1,2,... in the OUT canal\n"
        "LDI A 0\n"
        "LDI B 1\n"
        "loop:\n"
        "  OUT\n"
        "  ADD\n"
        "  JMP loop\n"),
    "Fibonacci": (
        "Seeds A=0, B=1; each step saves A in M0, adds, and reloads — "
        "a register dance across the side ponds.",
        "; 0 1 1 2 3 5 8 13 ...\n"
        "LDI A 0\n"
        "LDI B 1\n"
        "loop:\n"
        "  OUT\n"
        "  STA A 0\n"
        "  ADD\n"
        "  LDA B 0\n"
        "  JMP loop\n"),
    "Chasing bit": (
        "A single droplet rotates around the A canal (ROL) and pours into OUT.",
        "; one droplet circles the canal\n"
        "LDI A 1\n"
        "loop:\n"
        "  OUT\n"
        "  ROL\n"
        "  JMP loop\n"),
    "Memory demo": (
        "Stores two bytes in side ponds M0 / M1, then fetches them back.",
        "; side-pond store & fetch, then halt\n"
        "LDI A 0x0F\n"
        "STA A 0\n"
        "LDI A 0xF0\n"
        "STA A 1\n"
        "LDA A 0\n"
        "OUT\n"
        "LDA A 1\n"
        "OUT\n"
        "HLT\n"),
    "Countdown": (
        "DEC + CMP + JNZ: pours 10, 9, … 1 into OUT, then halts.",
        "; count 10 -> 1 then stop\n"
        "LDI A 10\n"
        "loop:\n"
        "  OUT\n"
        "  DEC A\n"
        "  LDI B 0\n"
        "  CMP\n"
        "  JNZ loop\n"
        "HLT\n"),
    "GCD (Euclid)": (
        "Subtract-and-swap GCD of 48 and 36 → 12. Uses CMP borrow (JC) + SWP.",
        "; GCD of A and B\n"
        "LDI A 48\n"
        "LDI B 36\n"
        "loop:\n"
        "  CMP\n"
        "  JZ done\n"
        "  JC swap      ; A < B -> swap\n"
        "  SUB          ; A = A - B\n"
        "  JMP loop\n"
        "swap:\n"
        "  SWP\n"
        "  JMP loop\n"
        "done:\n"
        "  OUT\n"
        "  HLT\n"),
    "Multiply (shift-add)": (
        "13 × 11 = 143 by the classic shift-and-add loop, using side ponds "
        "M0–M3 as scratch. The CPU's own MUL does this in one step.",
        "; 13 x 11 by shift & add\n"
        "LDI A 13\n"
        "STA A 2        ; multiplicand\n"
        "LDI A 11\n"
        "STA A 0        ; multiplier\n"
        "LDI A 0        ; accumulator\n"
        "loop:\n"
        "  LDA A 0\n"
        "  LDI B 0\n"
        "  CMP\n"
        "  JZ done\n"
        "  STA A 3      ; save acc\n"
        "  LDA A 0\n"
        "  LDI B 1\n"
        "  AND          ; A = mult & 1\n"
        "  JZ skip\n"
        "  LDA A 3\n"
        "  LDA B 2\n"
        "  ADD          ; acc += multiplicand\n"
        "  STA A 3\n"
        "skip:\n"
        "  LDA A 0\n"
        "  SHR A        ; mult >>= 1\n"
        "  STA A 0\n"
        "  LDA A 3\n"
        "  JMP loop\n"
        "done:\n"
        "  OUT\n"
        "  HLT\n"),
    "Gray code walk": (
        "A counts up in binary; OUT shows the Gray code — exactly one pound "
        "changes each step (gray = n ^ (n>>1)).",
        "; binary in A, gray in OUT\n"
        "LDI A 0\n"
        "loop:\n"
        "  STA A 0\n"
        "  MOV B A\n"
        "  SHR B        ; B = A >> 1\n"
        "  XOR          ; A = A ^ B\n"
        "  OUT\n"
        "  LDA A 0\n"
        "  INC A\n"
        "  JMP loop\n"),
    "Collatz (3n+1)": (
        "Starts at 27; OUT pours every term; halts when it reaches 1. "
        "Uses MUL, SHR and the side ponds.",
        "; Collatz for A (start 27)\n"
        "LDI A 27\n"
        "loop:\n"
        "  OUT\n"
        "  LDI B 1\n"
        "  CMP\n"
        "  JZ done\n"
        "  STA A 1\n"
        "  LDI B 1\n"
        "  AND          ; test odd\n"
        "  JZ even\n"
        "  LDA A 1\n"
        "  LDI B 3\n"
        "  MUL          ; A = 3A (low word)\n"
        "  INC A\n"
        "  JMP loop\n"
        "even:\n"
        "  LDA A 1\n"
        "  SHR A        ; A = A / 2\n"
        "  JMP loop\n"
        "done:\n"
        "  OUT\n"
        "  HLT\n"),
}

HELP_HTML = """
<h2>🌊 WATERGATE — Canal Lock Computer</h2>
<p>Each register is a flight of canal locks. Every pound is one bit:
<b>water = 1</b>, <b>dry = 0</b>. Loading a value sends a wave down the
flight while sluice gates lift. If arithmetic overflows, the source tower
<b>spills</b> — that is the carry flag.</p>

<h3>Editing pounds</h3>
<ul>
<li><b>Click</b> any pound to pour or drain it · <b>hover</b> to inspect.</li>
<li><b>Keyboard</b>: click a canal once, then <code>←/→</code> move the cursor,
<code>↑/↓</code> switch canal, <code>Space/Enter</code> toggles the pound.</li>
</ul>

<h3>Pour panel</h3>
<p>Formats: Decimal · Hex · Binary · <b>Text (ASCII)</b> — in text mode the
string's bytes are poured in big-endian (128-bit = 16 characters).</p>

<h3>Compute box</h3>
<p>Type an expression using <code>A</code>, <code>B</code>, <code>OUT</code>,
<code>M0…M15</code>, <code>bits</code>, integer literals (0x…, 0b…, 0o…),
operators <code>+ − * // % &lt;&lt; &gt;&gt; &amp; | ^ ~ −() **</code>, and
functions:</p>
<pre>popcount(x) reverse(x) swapb(x) clz(x) ctz(x)
hi(x) lo(x) sgn(x) gcd(a,b) isqrt(x) min max abs</pre>
<p>Negative results are fine — pouring them stores their two's complement.
Press <code>=</code> to evaluate, or <code>→ A / → B / → OUT</code> to pour.</p>

<h3>ALU</h3>
<pre>NOT AND OR XOR | ADD SUB MUL DIV | SHL SHR ROTL ROTR
A→OUT B→OUT | CMP NEG | REV BSWAP POP CLZ CTZ INC DEC ABS</pre>
<p>DIV: A = quotient, B = remainder, OUT = quotient. MUL keeps the low word;
the full product is shown in the log. With ⚡ ticked, ADD &amp; A−B run as a
visible ripple-carry.</p>

<h3>CPU instruction set</h3>
<pre>LDI r v        r ∈ {A,B} ← value
MOV d s        d ← s (A/B)
SWP            swap A and B
LDA r a        r ← M[a]        STA r a   M[a] ← r
ADD SUB AND OR XOR MUL         → A (OUT mirrors A); MUL: B = high word
NOT NEG INC DEC [r]            → r (default A)
SHL SHR ROL ROR [r]            → r (default A); C = bit out
CMP                            flags only (A−B)
OUT                            pour A into OUT
JMP t · JZ t · JNZ t · JC/JL t · JNC/JGE t
HLT                           NOP</pre>
<p>Labels: <code>loop:</code> · comments: <code>;</code> or <code>#</code>.</p>

<h3>Shortcuts</h3>
<pre>Ctrl+Z undo · Ctrl+Y redo · Ctrl+1…4 word size · F1 help</pre>
"""


# ------------------------------------------------------------ main window
OPS = [
    ("NOT A", "notA"), ("A AND B", "and"), ("A OR B", "or"), ("A XOR B", "xor"),
    ("A + B", "add"), ("A − B", "sub"), ("A × B", "mul"), ("A ÷ B", "div"),
    ("A << 1", "shl"), ("A >> 1", "shr"), ("ROTL A", "rol"), ("ROTR A", "ror"),
    ("A → OUT", "movA"), ("B → OUT", "movB"), ("CMP A−B", "cmp"), ("NEG A", "negA"),
]
TOOLS = [
    ("REV", "rev"), ("BSWAP", "bswap"), ("POP→A", "pop"), ("CLZ→A", "clz"),
    ("CTZ→A", "ctz"), ("INC A", "inc"), ("DEC A", "dec"), ("|A| ABS", "absA"),
]
EXPR_CHIPS = ["A + B", "A * B", "A ^ B", "gcd(A, B)"]
PATTERNS = [("0", "zero"), ("Max", "max"), ("0xAA", "aa"),
            ("0x55", "pat55"), ("LSB", "lsb"), ("MSB", "msb")]
UTILS = [
    ("Swap A ↔ B", "swap"), ("OUT → A", "outa"), ("OUT → B", "outb"),
    ("Clear A", "clrA"), ("Clear B", "clrB"), ("Fill A", "fillA"),
    ("Fill B", "fillB"), ("Rand A", "rndA"), ("Rand B", "rndB"),
]


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("WATERGATE — Canal Lock Computer (Compute Lab)")
        self.resize(1380, 900)

        self._applying = False
        self.flags = {"C": False, "Z": False, "S": False, "V": False}
        self.mem = [0] * MEM_SLOTS
        self.pc = 0
        self.history = []
        self.future = []
        self.ripple = None
        self.walker_pos = 0
        self.walker_prev = None
        self.log_no = 0

        self.canal = CanalWidget()
        self.canal.beginEdit.connect(self.push_history)
        self.canal.bitsEdited.connect(lambda _n: self.refresh())
        self.canal.editRowChanged.connect(self._sync_edit_row)

        self.ripple_timer = QTimer(self)
        self.ripple_timer.timeout.connect(self.ripple_step)
        self.demo_timer = QTimer(self)
        self.demo_timer.setInterval(1500)
        self.demo_timer.timeout.connect(self.demo_step)
        self.walker_timer = QTimer(self)
        self.walker_timer.timeout.connect(self.walker_step)
        self.cpu_timer = QTimer(self)
        self.cpu_timer.setInterval(450)
        self.cpu_timer.timeout.connect(self.cpu_step)

        # ----------------------------------------------------- right panel
        panel = QWidget()
        panel.setFixedWidth(378)
        pv = QVBoxLayout(panel)
        pv.setSpacing(7)

        # -- machine ------------------------------------------------------
        gb1 = QGroupBox("Machine & flow")
        g1 = QVBoxLayout(gb1)
        r1 = QHBoxLayout()
        r1.addWidget(QLabel("Machine:"))
        self.word_combo = QComboBox()
        self.word_combo.addItems(["16-bit", "32-bit", "64-bit", "128-bit"])
        self.word_combo.currentTextChanged.connect(self.change_word)
        r1.addWidget(self.word_combo, 1)
        r1.addWidget(QLabel("Edit:"))
        self.target_combo = QComboBox()
        self.target_combo.addItems(["A", "B", "OUT"])
        self.target_combo.currentTextChanged.connect(self.canal.set_edit_row)
        r1.addWidget(self.target_combo, 1)
        g1.addLayout(r1)
        r2 = QHBoxLayout()
        r2.addWidget(QLabel("Flow speed"))
        self.speed_slider = QSlider(Qt.Horizontal)
        self.speed_slider.setRange(25, 300)
        self.speed_slider.setValue(100)
        self.speed_slider.valueChanged.connect(
            lambda v: self.canal.set_speed(v / 100.0))
        r2.addWidget(self.speed_slider, 1)
        g1.addLayout(r2)
        self.ripple_chk = QCheckBox("⚡ Ripple-carry animation for ADD / SUB")
        self.ripple_chk.setChecked(True)
        self.ripple_chk.setToolTip(
            "When on, A+B / A−B are computed bit by bit from the LSB, with the "
            "carry visibly hopping over each sluice gate.")
        g1.addWidget(self.ripple_chk)
        pv.addWidget(gb1)

        # -- pour ---------------------------------------------------------
        gb3 = QGroupBox("Pour water in (load a value)")
        v3 = QVBoxLayout(gb3)
        self.fmt_combo = QComboBox()
        self.fmt_combo.addItems(["Decimal", "Hex", "Binary", "Text (ASCII)"])
        self.fmt_combo.currentIndexChanged.connect(self._pour_placeholder)
        v3.addWidget(self.fmt_combo)
        self.in_edit = QLineEdit()
        self.in_edit.returnPressed.connect(
            lambda: self.pour(self.target_combo.currentText()))
        self._pour_placeholder(0)
        v3.addWidget(self.in_edit)
        hb = QHBoxLayout()
        for label, target in (("💧 → A", "A"), ("💧 → B", "B"), ("💧 → OUT", "OUT")):
            btn = QPushButton(label)
            btn.clicked.connect(lambda _=False, t=target: self.pour(t))
            hb.addWidget(btn)
        v3.addLayout(hb)
        pv.addWidget(gb3)

        # -- compute box --------------------------------------------------
        gbx = QGroupBox("🧮 Compute — expression → canal")
        vx = QVBoxLayout(gbx)
        self.expr_in = QLineEdit()
        self.expr_in.setPlaceholderText("(A << 4) | 0xF   ·   gcd(A, B)   ·   popcount(A)+M0")
        self.expr_in.returnPressed.connect(lambda: self.compute(None))
        vx.addWidget(self.expr_in)
        chips = QHBoxLayout()
        for chip in EXPR_CHIPS:
            b = QPushButton(chip)
            b.setToolTip("Click to fill the expression box")
            b.clicked.connect(lambda _=False, c=chip: self.expr_in.setText(c))
            chips.addWidget(b)
        vx.addLayout(chips)
        r3 = QHBoxLayout()
        eq = QPushButton("＝")
        eq.setToolTip("Evaluate and show the result")
        eq.clicked.connect(lambda: self.compute(None))
        r3.addWidget(eq)
        for label, dest in (("→ A", "A"), ("→ B", "B"), ("→ OUT", "OUT")):
            b = QPushButton(label)
            b.clicked.connect(lambda _=False, d=dest: self.compute(d))
            r3.addWidget(b)
        vx.addLayout(r3)
        self.expr_out = QLineEdit()
        self.expr_out.setReadOnly(True)
        vx.addWidget(self.expr_out)
        pv.addWidget(gbx)

        # -- ALU ----------------------------------------------------------
        gb4 = QGroupBox("ALU — results pour into OUT")
        g4 = QGridLayout(gb4)
        g4.setSpacing(5)
        for i, (label, op) in enumerate(OPS):
            btn = QPushButton(label)
            btn.clicked.connect(lambda _=False, o=op: self.do_op(o))
            g4.addWidget(btn, i // 4, i % 4)
        hs = QHBoxLayout()
        hs.addWidget(QLabel("Shift by"))
        self.shift_spin = QSpinBox()
        self.shift_spin.setRange(1, 15)
        self.shift_spin.setValue(4)
        hs.addWidget(self.shift_spin)
        for label, op in (("A « k", "shlN"), ("A » k", "shrN"),
                          ("ROL k", "rolN"), ("ROR k", "rorN")):
            btn = QPushButton(label)
            btn.clicked.connect(lambda _=False, o=op: self.shift_k(o))
            hs.addWidget(btn)
        g4.addLayout(hs, 4, 0, 1, 4)
        pv.addWidget(gb4)

        # -- bit toolbox --------------------------------------------------
        gbt = QGroupBox("🧰 Bit toolbox (acts on A → OUT)")
        gt = QGridLayout(gbt)
        gt.setSpacing(5)
        for i, (label, op) in enumerate(TOOLS):
            btn = QPushButton(label)
            btn.clicked.connect(lambda _=False, o=op: self.do_op(o))
            gt.addWidget(btn, i // 4, i % 4)
        pv.addWidget(gbt)

        # -- CPU ----------------------------------------------------------
        gbc = QGroupBox("CPU — canal program")
        vc = QVBoxLayout(gbc)
        self.examples = QComboBox()
        self.examples.addItems(list(EXAMPLES.keys()))
        self.examples.currentTextChanged.connect(self.load_example)
        vc.addWidget(self.examples)
        self.example_desc = QLabel(" ")
        self.example_desc.setWordWrap(True)
        self.example_desc.setStyleSheet("color:#7f93a8; font-size:11px;")
        vc.addWidget(self.example_desc)
        rer = QHBoxLayout()
        lr_btn = QPushButton("⤓ Load")
        lr_btn.clicked.connect(self.load_selected)
        lrun_btn = QPushButton("⤓▶ Load & Run")
        lrun_btn.clicked.connect(self.load_and_run)
        clr_btn = QPushButton("✎ New")
        clr_btn.clicked.connect(self.new_program)
        rer.addWidget(lr_btn)
        rer.addWidget(lrun_btn)
        rer.addWidget(clr_btn)
        vc.addLayout(rer)
        self.prog_edit = QPlainTextEdit()
        self.prog_edit.setPlaceholderText("; write a program here…")
        self.prog_edit.setMinimumHeight(104)
        vc.addWidget(self.prog_edit)
        rc = QHBoxLayout()
        self.run_btn = QPushButton("▶ Run")
        self.run_btn.setCheckable(True)
        self.run_btn.toggled.connect(self.cpu_run_toggled)
        self.step_btn = QPushButton("⏭ Step")
        self.step_btn.clicked.connect(self.cpu_step)
        self.reset_btn = QPushButton("⟲ Reset")
        self.reset_btn.clicked.connect(self.cpu_reset)
        for b in (self.run_btn, self.step_btn, self.reset_btn):
            rc.addWidget(b)
        vc.addLayout(rc)
        sc = QHBoxLayout()
        sc.addWidget(QLabel("Step rate"))
        self.cpu_speed = QSlider(Qt.Horizontal)
        self.cpu_speed.setRange(100, 1200)
        self.cpu_speed.setValue(450)
        self.cpu_speed.valueChanged.connect(self.cpu_interval_changed)
        sc.addWidget(self.cpu_speed, 1)
        self.cpu_ms = QLabel("450 ms")
        sc.addWidget(self.cpu_ms)
        vc.addLayout(sc)
        self.pc_label = QLabel("PC 0")
        self.pc_label.setStyleSheet(
            "font-family:Consolas,monospace; color:#bfe3ff; font-weight:600;")
        vc.addWidget(self.pc_label)
        pv.addWidget(gbc)

        # -- memory side ponds -------------------------------------------
        gbm = QGroupBox("Memory side ponds (M0–M15)")
        vm = QVBoxLayout(gbm)
        mgrid = QGridLayout()
        mgrid.setSpacing(3)
        self.mem_group = QButtonGroup(self)
        self.mem_btns = []
        for i in range(MEM_SLOTS):
            b = QPushButton()
            b.setCheckable(True)
            b.setMinimumHeight(34)
            self.mem_group.addButton(b, i)
            self.mem_btns.append(b)
            mgrid.addWidget(b, i // 4, i % 4)
        self.mem_group.idClicked.connect(
            lambda i: self.status.setText(
                f"Side pond M{i} selected — transfers and LDA/STA use it."))
        self.mem_btns[0].setChecked(True)
        vm.addLayout(mgrid)
        hm = QHBoxLayout()
        for label, d in (("A→M", "A2M"), ("M→A", "M2A"),
                         ("B→M", "B2M"), ("M→B", "M2B")):
            btn = QPushButton(label)
            btn.clicked.connect(lambda _=False, dd=d: self.mem_xfer(dd))
            hm.addWidget(btn)
        vm.addLayout(hm)
        pv.addWidget(gbm)

        # -- patterns & utilities -----------------------------------------
        gb2 = QGroupBox("Patterns → selected canal")
        h2 = QHBoxLayout(gb2)
        for label, kind in PATTERNS:
            btn = QPushButton(label)
            btn.clicked.connect(lambda _=False, k=kind: self.apply_pattern(k))
            h2.addWidget(btn)
        pv.addWidget(gb2)

        gb5 = QGroupBox("Canal maintenance")
        g5 = QGridLayout(gb5)
        g5.setSpacing(5)
        for i, (label, op) in enumerate(UTILS):
            btn = QPushButton(label)
            btn.clicked.connect(lambda _=False, o=op: self.do_op(o))
            g5.addWidget(btn, i // 3, i % 3)
        pv.addWidget(gb5)

        # -- readouts -----------------------------------------------------
        gb7 = QGroupBox("OUT canal contents & float switches")
        v7 = QVBoxLayout(gb7)
        lamps = QHBoxLayout()
        self.lamp_carry = FlagLamp("CARRY", "#ffb054")
        self.lamp_zero = FlagLamp("ZERO", "#57e389")
        self.lamp_sign = FlagLamp("SIGN", "#b58cff")
        self.lamp_over = FlagLamp("OVER", "#ff6b6b")
        for lamp in (self.lamp_carry, self.lamp_zero,
                     self.lamp_sign, self.lamp_over):
            lamps.addWidget(lamp)
        v7.addLayout(lamps)
        self.out_dec = QLineEdit(); self.out_dec.setReadOnly(True)
        self.out_hex = QLineEdit(); self.out_hex.setReadOnly(True)
        self.out_bin = QLineEdit(); self.out_bin.setReadOnly(True)
        self.out_sgn = QLineEdit(); self.out_sgn.setReadOnly(True)
        self.out_txt = QLineEdit(); self.out_txt.setReadOnly(True)
        for label, w in (("DEC", self.out_dec), ("HEX", self.out_hex),
                         ("BIN", self.out_bin), ("SGN", self.out_sgn),
                         ("TXT", self.out_txt)):
            h = QHBoxLayout()
            lab = QLabel(label)
            lab.setFixedWidth(34)
            h.addWidget(lab)
            h.addWidget(w, 1)
            v7.addLayout(h)
        self.out_info = QLabel("")
        self.out_info.setStyleSheet("color:#7f93a8; font-size:11px;")
        v7.addWidget(self.out_info)
        pv.addWidget(gb7)

        # -- compute log --------------------------------------------------
        gbl = QGroupBox("📜 Compute log")
        vl = QVBoxLayout(gbl)
        self.log_view = QPlainTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setMaximumHeight(110)
        vl.addWidget(self.log_view)
        clr = QPushButton("Clear log")
        clr.clicked.connect(self.log_view.clear)
        vl.addWidget(clr)
        pv.addWidget(gbl)

        # -- records / export / demos -------------------------------------
        gb9 = QGroupBox("Records, export & demos")
        v9 = QVBoxLayout(gb9)
        r9a = QHBoxLayout()
        self.undo_btn = QPushButton("↩ Undo")
        self.undo_btn.setEnabled(False)
        self.undo_btn.clicked.connect(self.undo)
        self.redo_btn = QPushButton("↪ Redo")
        self.redo_btn.setEnabled(False)
        self.redo_btn.clicked.connect(self.redo)
        png_btn = QPushButton("📷 PNG")
        png_btn.clicked.connect(self.save_png)
        copy_btn = QPushButton("📋 Copy")
        copy_btn.clicked.connect(self.copy_state)
        help_btn = QPushButton("❓ Help")
        help_btn.clicked.connect(self.show_help)
        for b in (self.undo_btn, self.redo_btn, png_btn, copy_btn, help_btn):
            r9a.addWidget(b)
        v9.addLayout(r9a)
        r9b = QHBoxLayout()
        self.walker_btn = QPushButton("🚶 Bit walker")
        self.walker_btn.setCheckable(True)
        self.walker_btn.toggled.connect(self.toggle_walker)
        self.demo_btn = QPushButton("▶ Auto count-up demo")
        self.demo_btn.setCheckable(True)
        self.demo_btn.toggled.connect(self.toggle_demo)
        r9b.addWidget(self.walker_btn)
        r9b.addWidget(self.demo_btn)
        v9.addLayout(r9b)
        pv.addWidget(gb9)

        pv.addStretch(1)

        # ------------------------------------------------------ main layout
        central = QWidget()
        root = QHBoxLayout(central)
        root.setContentsMargins(10, 8, 10, 8)
        root.setSpacing(10)

        left = QWidget()
        lv = QVBoxLayout(left)
        lv.setContentsMargins(0, 0, 0, 0)
        lv.setSpacing(4)
        title = QLabel("🌊 WATERGATE — Canal Lock Computer")
        title.setStyleSheet("font-size:19px; font-weight:700; color:#bfe3ff;")
        sub = QLabel("Each canal pound is one bit — water = 1, dry = 0. "
                     "Click a pound to edit, or use the keyboard: arrows move, "
                     "Space toggles. Hover to inspect; F1 for full help.")
        sub.setWordWrap(True)
        sub.setStyleSheet("color:#7f93a8; font-size:12px;")
        lv.addWidget(title)
        lv.addWidget(sub)
        cscroll = QScrollArea()
        cscroll.setWidgetResizable(True)
        cscroll.setFrameShape(QFrame.NoFrame)
        cscroll.setWidget(self.canal)
        lv.addWidget(cscroll, 1)
        root.addWidget(left, 1)

        pscroll = QScrollArea()
        pscroll.setWidgetResizable(True)
        pscroll.setFrameShape(QFrame.NoFrame)
        pscroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        pscroll.setWidget(panel)
        pscroll.setFixedWidth(400)
        root.addWidget(pscroll)

        self.setCentralWidget(central)

        self.status = QLabel()
        self.statusBar().addWidget(self.status, 1)

        # ------------------------------------------------------- shortcuts
        for seq, fn in (("Ctrl+Z", self.undo), ("Ctrl+Y", self.redo),
                        ("Ctrl+Shift+Z", self.redo), ("F1", self.show_help)):
            sc2 = QShortcut(QKeySequence(seq), self)
            sc2.activated.connect(fn)
        for i, bits in enumerate((16, 32, 64, 128)):
            sc3 = QShortcut(QKeySequence(f"Ctrl+{i + 1}"), self)
            sc3.activated.connect(
                lambda b=bits: self.word_combo.setCurrentText(f"{b}-bit"))

        # ------------------------------------------------------- settings
        st = QSettings("Watergate", "CanalComputer")
        geo = st.value("geo")
        if geo:
            self.restoreGeometry(geo)
        word = st.value("word", "16-bit")
        if word in ("16-bit", "32-bit", "64-bit", "128-bit"):
            self.word_combo.setCurrentText(word)
        self.speed_slider.setValue(int(st.value("flow", 100)))
        self.cpu_speed.setValue(int(st.value("cpu", 450)))
        self.target_combo.setCurrentIndex(int(st.value("target", 0)))

        # initial program + welcome log
        self.prog_edit.setPlainText(EXAMPLES["Count up (loop)"][1])
        self.update_mem_buttons()
        self.log("WATERGATE booted — every pound of water is a 1.")
        self.log("Try: examples ▶ Load & Run, or type (A<<4)|0xF in Compute.")

        QTimer.singleShot(400, self._initial_load)
        self.refresh()

    # ------------------------------------------------------------- helpers
    def _sync_edit_row(self, name):
        self.target_combo.blockSignals(True)
        self.target_combo.setCurrentText(name)
        self.target_combo.blockSignals(False)

    def _pour_placeholder(self, idx):
        hints = ["e.g.  41234", "e.g.  A1F3  or  0xA1F3",
                 "e.g.  10110011", "e.g.  Hello, canal!"]
        self.in_edit.setPlaceholderText(hints[idx])

    def _initial_load(self):
        self.canal.set_value("A", 0b1011010011100110, flow=True)
        self.canal.set_value("B", 0b0101101000111101, flow=True)
        self.refresh()

    def cpu_interval_changed(self, v):
        self.cpu_timer.setInterval(v)
        self.cpu_ms.setText(f"{v} ms")

    def log(self, msg):
        self.log_no += 1
        self.log_view.appendPlainText(f"[{self.log_no:04d}] {msg}")
        if self.log_view.blockCount() > LOG_LIMIT:
            self.log_view.setMaximumBlockCount(LOG_LIMIT)
        sb = self.log_view.verticalScrollBar()
        sb.setValue(sb.maximum())

    def signed(self, x):
        n = self.canal.n
        return x - (1 << n) if (x >> (n - 1)) & 1 else x

    def rev_bits(self, x):
        n = self.canal.n
        r = 0
        for i in range(n):
            r = (r << 1) | ((x >> i) & 1)
        return r

    def bswap(self, x):
        by = self.canal.n // 8
        return int.from_bytes(x.to_bytes(by, "little"), "big")

    def _stop_ripple(self):
        if self.ripple is not None:
            self.ripple = None
            self.ripple_timer.stop()
            self.canal.set_focus(None)
            self.canal.set_locked(None)

    def stop_animations(self):
        self._stop_ripple()
        if self.demo_btn.isChecked():
            self.demo_btn.setChecked(False)
        if self.walker_btn.isChecked():
            self.walker_btn.setChecked(False)
        if self.run_btn.isChecked():
            self.run_btn.setChecked(False)

    # ------------------------------------------------------- undo / redo
    def snapshot(self):
        c = self.canal
        return {"n": c.n,
                "A": c.rows["A"].value, "B": c.rows["B"].value,
                "OUT": c.rows["OUT"].value,
                "flags": dict(self.flags), "mem": list(self.mem),
                "target": self.target_combo.currentIndex()}

    def push_history(self):
        self.history.append(self.snapshot())
        if len(self.history) > 250:
            del self.history[:-250]
        self.future.clear()
        self._sync_undo()

    def _sync_undo(self):
        self.undo_btn.setEnabled(bool(self.history))
        self.redo_btn.setEnabled(bool(self.future))

    def _apply(self, s):
        self._applying = True
        if s["n"] != self.canal.n:
            self.word_combo.setCurrentText(f"{s['n']}-bit")
        for k in ("A", "B", "OUT"):
            self.canal.set_value(k, s[k], flow=False)
        self.flags = dict(s["flags"])
        self.mem = list(s["mem"])
        self.target_combo.setCurrentIndex(s["target"])
        self._applying = False
        self.update_mem_buttons()
        self.refresh()
        self._sync_undo()

    def undo(self):
        if not self.history:
            return
        self.stop_animations()
        self.future.append(self.snapshot())
        self._apply(self.history.pop())
        self.status.setText("↩ Undo")

    def redo(self):
        if not self.future:
            return
        self.stop_animations()
        self.history.append(self.snapshot())
        self._apply(self.future.pop())
        self.status.setText("↪ Redo")

    # --------------------------------------------------------- word size
    def change_word(self, text):
        n = int(text.split("-")[0])
        if n == self.canal.n:
            return
        if not self._applying:
            self.stop_animations()
            self.push_history()
        self.canal.set_word_size(n)
        self.shift_spin.setMaximum(max(1, n - 1))
        self.mem = [v & self.canal.mask for v in self.mem]
        self.update_mem_buttons()
        self.refresh()

    def closeEvent(self, ev):
        st = QSettings("Watergate", "CanalComputer")
        st.setValue("geo", self.saveGeometry())
        st.setValue("word", self.word_combo.currentText())
        st.setValue("flow", self.speed_slider.value())
        st.setValue("cpu", self.cpu_speed.value())
        st.setValue("target", self.target_combo.currentIndex())
        super().closeEvent(ev)

    # -------------------------------------------------------------- pour
    def pour(self, target):
        if self.ripple is not None and target == "OUT":
            self.status.setText("Ripple-carry in progress — wait for it.")
            return
        fmt = self.fmt_combo.currentIndex()
        text = self.in_edit.text().strip()
        if not text:
            return
        warn = None
        if fmt == 3:  # Text
            raw = text.encode("ascii", "ignore")
            maxb = self.canal.n // 8
            if not raw:
                self.status.setText("⚠ No ASCII characters to pour.")
                return
            if len(raw) > maxb:
                raw = raw[-maxb:]
                warn = f"⚠ Text truncated to last {maxb} character(s)."
            v = int.from_bytes(raw, "big")
        else:
            t = text.replace("_", "").replace(" ", "")
            try:
                if fmt == 0:
                    v = int(t, 10)
                elif fmt == 1:
                    v = int(t[2:] if t.lower().startswith("0x") else t, 16)
                else:
                    if t.lower().startswith("0b"):
                        t = t[2:]
                    if not t or any(ch not in "01" for ch in t):
                        raise ValueError(t)
                    v = int(t, 2)
                if v < 0:
                    raise ValueError(t)
            except ValueError:
                self.status.setText("⚠ That value doesn't fit the selected format.")
                return
            if v > self.canal.mask:
                warn = f"⚠ Value too large for {self.canal.n} bits — masked."
                v &= self.canal.mask
        self.stop_animations()
        self.push_history()
        self.canal.set_value(target, v, flow=True)
        self.log(f"pour {target} ← {v} (0x{v:X})"
                 + (f"  ['{text}']" if fmt == 3 else ""))
        self.refresh()
        if warn:
            self.status.setText(warn)

    # ---------------------------------------------------------- patterns
    def apply_pattern(self, kind):
        self.stop_animations()
        self.push_history()
        c = self.canal
        n, mask = c.n, c.mask
        name = self.target_combo.currentText()
        if kind == "zero":
            v = 0
        elif kind == "max":
            v = mask
        elif kind == "aa":
            v = int("AA" * ((n + 7) // 8), 16) & mask
        elif kind == "pat55":
            v = int("55" * ((n + 7) // 8), 16) & mask
        elif kind == "lsb":
            v = 1
        else:
            v = 1 << (n - 1)
        c.set_value(name, v, flow=True)
        self.log(f"pattern {kind} → {name} = 0x{v:X}")
        self.refresh()

    # ---------------------------------------------------------- compute
    def build_env(self):
        c = self.canal
        n, mask, half = c.n, c.mask, c.n // 2
        env = {
            "A": c.rows["A"].value, "B": c.rows["B"].value,
            "OUT": c.rows["OUT"].value, "bits": n,
            "popcount": lambda x: bin(int(x)).count("1"),
            "reverse": lambda x: self.rev_bits(int(x) & mask),
            "swapb": lambda x: self.bswap(int(x) & mask),
            "clz": lambda x: (n - int(x).bit_length()) if x else n,
            "ctz": lambda x: ((int(x) & -int(x)).bit_length() - 1) if x else n,
            "hi": lambda x: (int(x) >> half) & ((1 << half) - 1),
            "lo": lambda x: int(x) & ((1 << half) - 1),
            "sgn": lambda x: self.signed(int(x) & mask),
            "gcd": math.gcd, "isqrt": math.isqrt,
            "min": min, "max": max, "abs": abs,
        }
        for i, v in enumerate(self.mem):
            env[f"M{i}"] = v
        return env

    def compute(self, dest):
        expr = self.expr_in.text().strip()
        if not expr:
            return
        try:
            raw = safe_eval(expr, self.build_env())
        except Exception as e:
            self.expr_out.setText("⚠ error")
            self.status.setText(f"Compute error: {e}")
            self.log(f"compute {expr!r} → ERROR ({e})")
            return
        masked = raw & self.canal.mask
        note = "" if raw == masked else f"   (masked from {raw})"
        self.expr_out.setText(f"{masked}   (0x{masked:X}){note}")
        self.log(f"compute {expr} = {masked} (0x{masked:X})")
        if dest:
            self.stop_animations()
            self.push_history()
            self.canal.set_value(dest, masked, flow=True)
            self.log(f"compute result poured → {dest}")
        self.refresh()

    # --------------------------------------------------------------- ALU
    def do_op(self, op):
        self.stop_animations()
        self.push_history()
        c = self.canal
        n, mask = c.n, c.mask
        R = c.rows
        A, B = R["A"].value, R["B"].value
        msb = n - 1
        sb = lambda x: (x >> msb) & 1

        # --- utilities first -------------------------------------------
        if op in ("swap", "outa", "outb") or op.startswith(("clr", "fill", "rnd")):
            if op == "swap":
                c.set_value("A", B)
                c.set_value("B", A)
                self.log("swap A <-> B")
            elif op == "outa":
                c.set_value("A", R["OUT"].value)
                self.log("OUT -> A")
            elif op == "outb":
                c.set_value("B", R["OUT"].value)
                self.log("OUT -> B")
            elif op.startswith("clr"):
                c.set_value(op[3], 0)
            elif op.startswith("fill"):
                c.set_value(op[4], mask)
            else:
                c.set_value(op[3], random.getrandbits(n))
            self.refresh()
            return

        carry = over = None
        C = 0

        if op in ("add", "sub") and self.ripple_chk.isChecked():
            self.start_ripple(A, B, sub=(op == "sub"))
            return

        if op == "notA":
            C = ~A & mask
            carry = over = False
        elif op == "and":
            C = A & B; carry = over = False
        elif op == "or":
            C = A | B; carry = over = False
        elif op == "xor":
            C = A ^ B; carry = over = False
        elif op == "add":
            full = A + B
            C = full & mask
            carry = full > mask
            over = sb(A) == sb(B) and sb(C) != sb(A)
        elif op == "sub":
            C = (A - B) & mask
            carry = A < B
            over = sb(A) != sb(B) and sb(C) != sb(A)
        elif op == "mul":
            full = A * B
            C = full & mask
            carry = full > mask
            over = False
            extra = f"  full product = {full} (high word 0x{full >> n:X})"
        elif op == "div":
            if B == 0:
                self.flags["V"] = True
                self.status.setText("⚠ Divide by zero — OVER lamp lit.")
                self.log("div by zero → OVER flag")
                self.refresh()
                return
            q, r = divmod(A, B)
            c.set_value("A", q)
            c.set_value("B", r)
            C = q
            carry, over = False, False
            extra = f"  quotient {q} (0x{q:X}), remainder {r}"
        elif op == "shl":
            carry = bool(sb(A)); C = (A << 1) & mask; over = False
        elif op == "shr":
            carry = bool(A & 1); C = A >> 1; over = False
        elif op == "rol":
            carry = bool(sb(A)); C = ((A << 1) | (A >> msb)) & mask; over = False
        elif op == "ror":
            carry = bool(A & 1); C = ((A >> 1) | ((A & 1) << msb)) & mask; over = False
        elif op == "movA":
            C = A
        elif op == "movB":
            C = B
        elif op == "negA":
            C = (-A) & mask; carry = False; over = False
        elif op == "cmp":
            res = (A - B) & mask
            self.flags["C"] = (A < B)
            self.flags["V"] = sb(A) != sb(B) and sb(res) != sb(A)
            self.flags["Z"] = (res == 0)
            self.flags["S"] = bool(sb(res))
            self.log(f"CMP A-B = {res} → flags "
                     f"(borrow={int(A < B)})")
            self.refresh()
            self.status.setText(
                f"CMP: A−B = {res} → flags updated (borrow={int(A < B)})")
            return
        else:
            C = self.bit_tool(op, A)
            carry = over = False

        c.set_value("OUT", C, flow=True)
        self.flags["Z"] = (C == 0)
        self.flags["S"] = bool(sb(C))
        if carry is not None:
            self.flags["C"] = bool(carry)
        if over is not None:
            self.flags["V"] = bool(over)
        label = {"notA": "NOT A", "movA": "A→OUT", "movB": "B→OUT",
                 "negA": "NEG A"}.get(op, op.upper())
        msg = f"{label} → OUT = {C} (0x{C:X})" + \
              ("  " + extra) if op in ("mul", "div") and 'extra' in dir() else \
              f"{label} → OUT = {C} (0x{C:X})"
        self.status.setText(msg)
        self.log(msg)

    def bit_tool(self, op, A):
        n, mask = self.canal.n, self.canal.mask
        if op == "rev":
            return self.rev_bits(A)
        if op == "bswap":
            return self.bswap(A)
        if op == "pop":
            return bin(A).count("1")
        if op == "clz":
            return (n - A.bit_length()) if A else n
        if op == "ctz":
            return ((A & -A).bit_length() - 1) if A else n
        if op == "inc":
            self.flags["C"] = (A == mask)
            return (A + 1) & mask
        if op == "dec":
            self.flags["C"] = (A == 0)      # borrow
            return (A - 1) & mask
        if op == "absA":
            return abs(self.signed(A)) & mask
        return 0

    def shift_k(self, op):
        self.stop_animations()
        self.push_history()
        c = self.canal
        n, mask = c.n, c.mask
        A = c.rows["A"].value
        k = max(1, min(n - 1, self.shift_spin.value()))
        msb = n - 1
        if op == "shlN":
            C = (A << k) & mask
            carry = bool((A >> (n - k)) & 1)
        elif op == "shrN":
            C = A >> k
            carry = bool((A >> (k - 1)) & 1)
        elif op == "rolN":
            C = ((A << k) | (A >> (n - k))) & mask
            carry = bool((A >> (n - k)) & 1)
        else:
            C = ((A >> k) | ((A & ((1 << k) - 1)) << (n - k))) & mask
            carry = bool((A >> (k - 1)) & 1)
        c.set_value("OUT", C, flow=True)
        self.flags["C"] = carry
        self.flags["V"] = False
        self.flags["Z"] = (C == 0)
        self.flags["S"] = bool((C >> msb) & 1)
        msg = f"{op[:-1].upper()} by {k} → OUT = {C} (0x{C:X})"
        self.status.setText(msg)
        self.log(msg)
        self.refresh()

    # ------------------------------------------------------ ripple-carry
    def start_ripple(self, a, b, sub):
        c = self.canal
        n, mask = c.n, c.mask
        self.ripple = {"a": a & mask,
                       "b": ((~b) & mask) if sub else (b & mask),
                       "b_orig": b & mask,
                       "sub": sub, "i": 0,
                       "c": 1 if sub else 0, "res": 0}
        c.set_value("OUT", 0, flow=False)
        c.set_locked("OUT")
        self.ripple_timer.start(max(25, min(400, int(110 / c.speed_mult))))
        self.status.setText("Ripple-carry: water pushes carry pound by pound…")

    def ripple_step(self):
        r = self.ripple
        if r is None:
            self.ripple_timer.stop()
            return
        c = self.canal
        n = c.n
        p = r["i"]
        ai = (r["a"] >> p) & 1
        bi = (r["b"] >> p) & 1
        s = ai + bi + r["c"]
        bit = s & 1
        r["c"] = s >> 1
        r["res"] |= bit << p
        c.poke_bit("OUT", p, bit, wiggle=False)
        c.set_focus(n - 1 - p)
        if r["c"]:
            g = n - 2 - p
            if g >= 0:
                c.add_pulse(g)
        r["i"] += 1
        if r["i"] >= n:
            self.finish_ripple()
        else:
            self.status.setText(
                f"Ripple-carry: pound {r['i']}/{n} … carry = {r['c']}")

    def finish_ripple(self):
        r = self.ripple
        self.ripple = None
        self.ripple_timer.stop()
        c = self.canal
        n = c.n
        c.set_focus(None)
        c.set_locked(None)
        res, co = r["res"], r["c"]
        sb = lambda x: (x >> (n - 1)) & 1
        if r["sub"]:
            borrow = (co == 0)
            self.flags["C"] = borrow
            self.flags["V"] = sb(r["a"]) != sb(r["b_orig"]) and sb(res) != sb(r["a"])
            msg = f"Ripple SUB → OUT = {res} (borrow = {int(borrow)})"
        else:
            self.flags["C"] = bool(co)
            self.flags["V"] = sb(r["a"]) == sb(r["b_orig"]) and sb(res) != sb(r["a"])
            msg = f"Ripple ADD → OUT = {res} (final carry = {co})"
        self.flags["Z"] = (res == 0)
        self.flags["S"] = bool(sb(res))
        self.log(msg)
        self.refresh()
        self.status.setText(msg)

    # ------------------------------------------------------------- demos
    def toggle_demo(self, on):
        self.demo_btn.setText("⏸ Stop count-up demo" if on
                              else "▶ Auto count-up demo")
        if on:
            self._stop_ripple()
            if self.walker_btn.isChecked():
                self.walker_btn.setChecked(False)
            if self.run_btn.isChecked():
                self.run_btn.setChecked(False)
            self.demo_step()
            self.demo_timer.start()
        else:
            self.demo_timer.stop()

    def demo_step(self):
        c = self.canal
        nxt = c.rows["OUT"].value + 1
        c.set_value("OUT", nxt & c.mask, flow=True)
        self.flags["C"] = nxt > c.mask
        self.refresh()

    def toggle_walker(self, on):
        if on:
            self._stop_ripple()
            if self.demo_btn.isChecked():
                self.demo_btn.setChecked(False)
            if self.run_btn.isChecked():
                self.run_btn.setChecked(False)
            name = self.target_combo.currentText()
            self.canal.set_value(name, 0, flow=False)
            self.walker_prev = None
            self.walker_pos = self.canal.n - 1
            self.walker_timer.start(150)
            self.status.setText(f"🚶 Bit walker marching across '{name}'.")
        else:
            self.walker_timer.stop()

    def walker_step(self):
        name = self.target_combo.currentText()
        c = self.canal
        if self.walker_prev is not None:
            c.poke_bit(name, self.walker_prev, 0, wiggle=False)
        c.poke_bit(name, self.walker_pos, 1)
        self.walker_prev = self.walker_pos
        self.walker_pos = (self.walker_pos - 1) % c.n
        self.refresh()

    # --------------------------------------------------------------- CPU
    def compile_program(self):
        labels = {}
        prog = []
        for ln, raw in enumerate(self.prog_edit.toPlainText().splitlines()):
            line = raw.split(";")[0].split("#")[0].strip()
            while True:
                m = re.match(r"^([A-Za-z_]\w*)\s*:\s*(.*)$", line)
                if not m:
                    break
                labels[m.group(1).lower()] = len(prog)
                line = m.group(2).strip()
            if not line:
                continue
            parts = re.split(r"[\s,]+", line)
            prog.append((ln, parts[0].upper(), parts[1:]))
        return prog, labels

    def resolve(self, tok, labels):
        t = tok.strip().lower()
        if t in labels:
            return labels[t]
        if t.startswith("0x"):
            return int(t[2:], 16)
        if t.startswith("0b"):
            return int(t[2:], 2)
        return int(t, 10)

    def reg_or(self, args, default="A"):
        if not args:
            return default
        r = args[0].upper()
        if r not in ("A", "B"):
            raise ValueError(args[0])
        return r

    def load_selected(self):
        name = self.examples.currentText()
        desc, code = EXAMPLES.get(name, ("", ""))
        if not code:
            self.status.setText("Pick an example from the list first.")
            return
        self.run_btn.setChecked(False)
        self.prog_edit.setPlainText(code)
        self.cpu_reset()

    def load_and_run(self):
        self.load_selected()
        if self.prog_edit.toPlainText().strip():
            self.run_btn.setChecked(True)

    def new_program(self):
        self.run_btn.setChecked(False)
        self.prog_edit.setPlainText("; new program\n")
        self.cpu_reset()

    def load_example(self, name):
        desc, code = EXAMPLES.get(name, ("", ""))
        if code:
            self.example_desc.setText(desc)

    def cpu_run_toggled(self, on):
        if on:
            self._stop_ripple()
            if self.demo_btn.isChecked():
                self.demo_btn.setChecked(False)
            if self.walker_btn.isChecked():
                self.walker_btn.setChecked(False)
            prog, _ = self.compile_program()
            if not prog:
                self.run_btn.setChecked(False)
                self.status.setText("No program to run.")
                return
            self.cpu_timer.start()
            self.status.setText("▶ Running program…")
        else:
            self.cpu_timer.stop()

    def cpu_reset(self):
        self.run_btn.setChecked(False)
        self.pc = 0
        self.highlight_line(None)
        self.pc_label.setText("PC 0")
        self.status.setText("CPU reset — PC = 0.")

    def cpu_step(self):
        self._stop_ripple()
        if self.demo_btn.isChecked():
            self.demo_btn.setChecked(False)
        if self.walker_btn.isChecked():
            self.walker_btn.setChecked(False)

        prog, labels = self.compile_program()
        if not prog:
            self.run_btn.setChecked(False)
            self.status.setText("No program to run.")
            return
        if self.pc >= len(prog):
            self.run_btn.setChecked(False)
            self.highlight_line(None)
            self.status.setText("PC ran past the end — add HLT.")
            return

        self.push_history()
        ln, op, args = prog[self.pc]
        self.pc += 1

        c = self.canal
        n, mask = c.n, c.mask
        R = c.rows
        msb = n - 1
        sb = lambda x: (x >> msb) & 1
        err = None

        def set_flags(res, carry=None, over=None):
            self.flags["Z"] = (res == 0)
            self.flags["S"] = bool(sb(res))
            if carry is not None:
                self.flags["C"] = bool(carry)
            if over is not None:
                self.flags["V"] = bool(over)

        try:
            if op == "NOP":
                pass
            elif op == "LDI":
                reg = self.reg_or(args[:1]) if args and args[0].upper() in ("A", "B") \
                    else None
                if reg is None:
                    raise ValueError(args[0] if args else "missing register")
                c.set_value(reg, self.resolve(args[1], labels) & mask)
            elif op == "MOV":
                dst, src = args[0].upper(), args[1].upper()
                if dst not in ("A", "B") or src not in ("A", "B"):
                    raise ValueError(op)
                c.set_value(dst, R[src].value)
            elif op == "SWP":
                c.set_value("A", R["B"].value)
                c.set_value("B", R["A"].value)
            elif op == "LDA":
                reg = self.reg_or(args[:1])
                addr = self.resolve(args[1], labels)
                if not (0 <= addr < MEM_SLOTS):
                    raise ValueError(args[1])
                c.set_value(reg, self.mem[addr])
            elif op == "STA":
                reg = self.reg_or(args[:1])
                addr = self.resolve(args[1], labels)
                if not (0 <= addr < MEM_SLOTS):
                    raise ValueError(args[1])
                self.mem[addr] = R[reg].value
                self.update_mem_buttons()
            elif op in ("ADD", "SUB", "AND", "OR", "XOR", "MUL", "CMP"):
                A, Bv = R["A"].value, R["B"].value
                write = True
                if op == "ADD":
                    full = A + Bv
                    res = full & mask
                    carry, over = full > mask, sb(A) == sb(Bv) and sb(res) != sb(A)
                elif op == "SUB":
                    res = (A - Bv) & mask
                    carry, over = A < Bv, sb(A) != sb(Bv) and sb(res) != sb(A)
                elif op == "AND":
                    res, carry, over = A & Bv, False, False
                elif op == "OR":
                    res, carry, over = A | Bv, False, False
                elif op == "XOR":
                    res, carry, over = A ^ Bv, False, False
                elif op == "MUL":
                    full = A * Bv
                    res = full & mask
                    c.set_value("B", (full >> n) & mask)
                    carry, over = full > mask, False
                else:  # CMP
                    write = False
                    res = (A - Bv) & mask
                    carry, over = A < Bv, sb(A) != sb(Bv) and sb(res) != sb(A)
                if write:
                    c.set_value("A", res)
                    c.set_value("OUT", res, flow=False)
                set_flags(res, carry, over)
            elif op in ("NOT", "NEG", "INC", "DEC", "SHL", "SHR", "ROL", "ROR"):
                r = self.reg_or(args)
                v = R[r].value
                if op == "NOT":
                    res, carry, over = ~v & mask, False, False
                elif op == "NEG":
                    res, carry, over = (-v) & mask, False, (v == 1 << msb)
                elif op == "INC":
                    res, carry, over = (v + 1) & mask, (v == mask), False
                elif op == "DEC":
                    res, carry, over = (v - 1) & mask, (v == 0), False
                elif op == "SHL":
                    res, carry, over = (v << 1) & mask, bool(sb(v)), False
                elif op == "SHR":
                    res, carry, over = v >> 1, bool(v & 1), False
                elif op == "ROL":
                    res = ((v << 1) | (v >> msb)) & mask
                    carry, over = bool(sb(v)), False
                else:
                    res = ((v >> 1) | ((v & 1) << msb)) & mask
                    carry, over = bool(v & 1), False
                c.set_value(r, res)
                c.set_value("OUT", res, flow=False)
                set_flags(res, carry, over)
            elif op == "OUT":
                c.set_value("OUT", R["A"].value, flow=True)
                self.log(f"CPU OUT pour: {R['A'].value} (0x{R['A'].value:X})")
            elif op in ("JMP", "JZ", "JNZ", "JC", "JNC", "JL", "JGE"):
                tgt = self.resolve(args[0], labels)
                take = {"JMP": True, "JZ": self.flags["Z"],
                        "JNZ": not self.flags["Z"], "JC": self.flags["C"],
                        "JL": self.flags["C"], "JNC": not self.flags["C"],
                        "JGE": not self.flags["C"]}[op]
                if take:
                    self.pc = tgt
            elif op == "HLT":
                self.run_btn.setChecked(False)
                self.highlight_line(ln)
                self.pc_label.setText(f"PC {self.pc} · HLT")
                self.log("CPU halted.")
                self.refresh()
                self.status.setText("HLT — the canal system is at rest.")
                return
            else:
                err = f"Unknown instruction '{op}'"
        except (ValueError, IndexError) as e:
            err = f"Bad operand {e}"

        if err:
            self.run_btn.setChecked(False)
            self.highlight_line(ln)
            self.log(f"CPU error line {ln + 1}: {err}")
            self.refresh()
            self.status.setText("⚠ " + err)
            return

        if self.pc < len(prog):
            self.highlight_line(prog[self.pc][0])
            self.pc_label.setText(f"PC {self.pc} · {prog[self.pc][1]}")
        else:
            self.highlight_line(None)
            self.pc_label.setText(f"PC {self.pc} · end")
            self.run_btn.setChecked(False)
        self.refresh()
        self.status.setText(f"{op} · PC={self.pc}")

    def highlight_line(self, ln):
        doc = self.prog_edit.document()
        sels = []
        if ln is not None and 0 <= ln < doc.blockCount():
            es = QTextEdit.ExtraSelection()
            es.cursor = QTextCursor(doc.findBlockByNumber(ln))
            es.cursor.clearSelection()
            es.format.setBackground(QColor("#14405e"))
            es.format.setProperty(QTextFormat.FullWidthSelection, True)
            sels.append(es)
        self.prog_edit.setExtraSelections(sels)

    # ------------------------------------------------------------ memory
    def update_mem_buttons(self):
        hd = self.canal.n // 4
        for i, b in enumerate(self.mem_btns):
            v = self.mem[i]
            h = format(v, "X")
            if hd > 8:
                disp = (h[:4] + "…" + h[-4:]) if len(h) > 8 else h
            else:
                disp = format(v, "0%dX" % hd)
            b.setText(f"M{i}\n{disp}")
            b.setToolTip(f"M{i} = {v}  (0x{h})")

    def mem_xfer(self, direction):
        addr = self.mem_group.checkedId()
        if addr < 0:
            return
        self.stop_animations()
        self.push_history()
        R = self.canal.rows
        if direction == "A2M":
            self.mem[addr] = R["A"].value
        elif direction == "M2A":
            self.canal.set_value("A", self.mem[addr])
        elif direction == "B2M":
            self.mem[addr] = R["B"].value
        else:
            self.canal.set_value("B", self.mem[addr])
        self.update_mem_buttons()
        self.log(f"side pond transfer {direction} at M{addr}")
        self.refresh()
        self.status.setText(f"Side pond transfer done at M{addr}.")

    # ------------------------------------------------------ export / help
    def save_png(self):
        path, _ = QFileDialog.getSaveFileName(
            self, "Save screenshot", "watergate.png", "PNG images (*.png)")
        if path:
            self.grab().save(path)
            self.status.setText(f"Saved screenshot → {path}")

    def copy_state(self):
        c = self.canal
        n = c.n
        a, b, o = c.rows["A"].value, c.rows["B"].value, c.rows["OUT"].value
        f = self.flags
        txt = (f"WATERGATE {n}-bit state\n"
               f"A   = {a}  0x{a:X}  {a:0{n}b}\n"
               f"B   = {b}  0x{b:X}  {b:0{n}b}\n"
               f"OUT = {o}  0x{o:X}  {o:0{n}b}\n"
               f"flags: C={int(f['C'])} Z={int(f['Z'])} "
               f"S={int(f['S'])} V={int(f['V'])}\n"
               f"mem: {[hex(x) for x in self.mem]}")
        QApplication.clipboard().setText(txt)
        self.status.setText("📋 State copied to clipboard.")

    def show_help(self):
        dlg = QDialog(self)
        dlg.setWindowTitle("WATERGATE — Help")
        v = QVBoxLayout(dlg)
        tb = QTextBrowser()
        tb.setHtml(HELP_HTML)
        v.addWidget(tb)
        btn = QPushButton("Close")
        btn.clicked.connect(dlg.accept)
        v.addWidget(btn)
        dlg.resize(660, 680)
        dlg.exec()

    # ------------------------------------------------------------ refresh
    def refresh(self):
        c = self.canal
        n = c.n
        a = c.rows["A"].value
        b = c.rows["B"].value
        out = c.rows["OUT"].value
        c.carry = self.flags["C"]
        self.out_dec.setText(str(out))
        self.out_hex.setText("0x" + format(out, "0%dX" % (n // 4)))
        self.out_bin.setText(format(out, "0%db" % n))
        sgn = self.signed(out)
        self.out_sgn.setText(str(sgn))
        raw = out.to_bytes(n // 8, "big")
        self.out_txt.setText("".join(
            chr(ch) if 32 <= ch < 127 else "·" for ch in raw))
        pop = bin(out).count("1")
        self.out_info.setText(
            f"Flooded pounds: {pop} / {n}      Signed: {sgn}")
        self.lamp_carry.set_on(self.flags["C"])
        self.lamp_zero.set_on(out == 0)
        self.lamp_sign.set_on(bool((out >> (n - 1)) & 1))
        self.lamp_over.set_on(self.flags["V"])
        self.status.setText(
            f"{n}-bit · A={a} (0x{a:X}) · B={b} (0x{b:X}) · "
            f"OUT={out} (0x{out:X}) · C={int(self.flags['C'])} "
            f"Z={int(self.flags['Z'])} S={int(self.flags['S'])} "
            f"V={int(self.flags['V'])}")


def main():
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setStyleSheet(STYLESHEET)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()