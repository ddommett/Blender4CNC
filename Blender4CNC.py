# Blender4CNC - Design 3-axis CNC projects in Blender and produce G-Code.
# Copyright (C) 2023  David Dommett

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

bl_info = {
    "name": "Blender4CNC",
    'category': 'GCode',
    'author': '',
    'version': (1, 0, 0),
    'blender': (3, 4, 1),
    'location': '3D_Viewport window -> N-Panel > GCode',
    'description': 'Blender 4 CNC'
}

#*******************************************************************
# Run utility code to turn on/off coverage and debug statements
# All functions take Py2GCode_28.py and output to Py2GCode_28_Out.py
# (Turn off DEBUG before turning on coverage)
# Run:
# python3 TurnOnCoverage.py to add in coverage code lines 
# python3 TurnOffCoverage.py to remove coverage code lines 
# python3 TurnOnDEBUG.py to un-comment all DEBUG lines 
# python3 TurnOffDEBUG.py to comment all DEBUG lines 
#*******************************************************************

import sys

#*******************************************************************
# Check we can find numpy, scipy and scikit-image
#*******************************************************************
notFound = ""
try:
    import numpy
except:
    notFound += "numpy "
try:
    import scipy
except:
    notFound += "scipy "
try:
    import skimage
except:
    notFound += "scikit-image "
if notFound != "":
    raise Exception("ERROR Could not find packages: " + notFound)
    
from   ast import literal_eval
import bmesh                # Handling Blender objects in edit mode
import bpy
from   bpy.props import (StringProperty, PointerProperty, FloatProperty, IntProperty, BoolProperty)
from   bpy.types import (Panel, Operator, AddonPreferences, PropertyGroup, )
import cmath
import copy
import cProfile             # Used for performance profiling with 'runctx'
                            # A good place to profile from is: class ProcessPaths
import datetime
from   functools import reduce
import glob
import inspect
import io
import math
from   math import *
import mathutils
from   mathutils import *    # Blender's Vector class
import numpy
import operator
import os                   # Handling paths, removing files etc.
import re                   # Regular expressions (used in e.g. processing GCode)
import shlex                # Used to split strings properly for shell to call subprocess etc. (e.g. to call ImageMagick)
import subprocess           # Used to create a process (e.g. ImageMagick)
import scipy                # Used for image morphology on numpy arrays
import scipy.ndimage        #
import scipy.misc           #
import skimage              # Used for drawing shapes onto numpy arrays as images
import skimage.draw         #
import skimage.transform    #
import skimage.morphology   # Used for flood filling
import sys
import time
import mmap
import shutil
import random               # Used for uniform

# Increase the max number of recursive calls
# This is important for the CSG functions
sys.setrecursionlimit(10000) # my default is 1000, increasing too much may cause a seg fault

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A Class to handle converting a Blender model (project) into GCode
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class Blender4CNC:

    coverage = {}
    REGRESSION_TEST_DRAW_OUTPUTS = False
    DEBUG_DEPTH_IMAGES = False
        
    #**************************************************************************
    # Global static functions and constants
    #**************************************************************************
    INCHES_TO_METERS = 25.4 / 1000.0
    METERS_TO_INCHES = 1000.0 / 25.4

    # These also are hard-coded into the FloatsAreEqual function for performance
    # - saves about 30% and this gets called A LOT!!!!!!!!!!!!!
    REL_TOLERANCE = 1e-5
    ABS_TOLERANCE = 1e-9

    #**************************************************************************
    # 
    #**************************************************************************
    def GetzSZ():
        if (bpy.context.scene.unit_settings.system == "METRIC"):
            return (0.001, 0.05)
        else:
            return (0.01 * 1 / Blender4CNC.METERS_TO_INCHES, 1 / Blender4CNC.METERS_TO_INCHES)  # 1 inch

    #**************************************************************************
    # Return True if the two floats are VERY close (equal within an error)
    #**************************************************************************
    # FLT_EPSILON in C/C++ is 1e-5 or smaller for floats
    # FLT_EPSILON in C/C++ is 1e-9 or smaller for doubles
    #The following definitions are from The art of computer programming by Knuth:
    #bool approximatelyEqual(float a, float b, float epsilon)
    #{
    #    return fabs(a - b) <= ( (fabs(a) < fabs(b) ? fabs(b) : fabs(a)) * epsilon);
    #}
    #bool essentiallyEqual(float a, float b, float epsilon)
    #{
    #    return fabs(a - b) <= ( (fabs(a) > fabs(b) ? fabs(b) : fabs(a)) * epsilon);
    #}
    #bool definitelyGreaterThan(float a, float b, float epsilon)
    #{
    #    return (a - b) > ( (fabs(a) < fabs(b) ? fabs(b) : fabs(a)) * epsilon);
    #}
    #bool definitelyLessThan(float a, float b, float epsilon)
    #{
    #    return (b - a) > ( (fabs(a) < fabs(b) ? fabs(b) : fabs(a)) * epsilon);
    #}
    #    
    def FloatsAreEqual(a, b):
#        return math.isclose(a, b, rel_tol=Blender4CNC.REL_TOLERANCE, abs_tol=Blender4CNC.ABS_TOLERANCE)
        return math.isclose(a, b, rel_tol=1e-5, abs_tol=1e-9)

    #********************************************************************
    # Returns True if float a is between a1 and a2 (allowing for the 
    # specified error amount if nearly equal)
    #********************************************************************
    def FloatIsBetween(a, a1, a2):
        return ((a1 - Blender4CNC.REL_TOLERANCE) <= a <= (a2 + Blender4CNC.REL_TOLERANCE))

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Structure class to hold current position and entrance direction when tracing blobs in images
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    class MyPix:

        def __init__(self, x2, y2, dx2, dy2):
            self.x = int(x2)
            self.y = int(y2)
            self.dx = int(dx2)
            self.dy = int(dy2)

        def __repr__(self):
            return "(" + str(self.x) + ", " + str(self.y) + ", " + str(self.dx) + ", " + str(self.dy) + ")"

        def IsLocationEqual(self, p):
            return ((self.x == p.x) and (self.y == p.y))

        def IsDirectionEqual(self, p):
            return ((self.dx == p.dx) and (self.dy == p.dy))

        def ToString(self):
         return "%d,%d,%d,%d" % (self.x,self.y,self.dx,self.dy)

        def InsideArea(self, xMin, xMax, yMin, yMax):
            return ((self.x >= xMin) and (self.x <= xMax) and (self.y >= yMin) and (self.y <= yMax))

        def MoveInDirection(self):
            self.x += int(self.dx)
            self.y += int(self.dy)

        def Rotate180(self):
            self.dy = int(-self.dy)
            self.dx = int(-self.dx)

        # Rotating cw by 90 Matrix
        #  0, 1
        # -1, 0
        # New x = old y, New y = -old x
        def Rotate90CW(self):
            t = int(self.dy)
            self.dy = int(-self.dx)
            self.dx = int(t)

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A Class to generate programmatic GCode
    # Has public functions:
    #   CutCircularPocket
    #   CutPocket
    #   CutPocketNoRough
    #   CutCircle
    #   CutShapeLine
    #   DrillCycle
    #   GetSpeedGCodeStr
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS Pockets
    class Pockets:
        
#        #********************************************************************
#        # Regression Tests
#        #********************************************************************
#        def Test_Regression(self):
#            poly = Blender4CNC.Polytoxogon([(0,0)])
#            poly.Test_Regression()

        #********************************************************************
        # 
        #********************************************************************
        def DEBUG_METHOD_HEADER(self, tf = False):
            methodName = self.__class__.__name__ + "." + inspect.stack()[1][3]
            indent = None
            self.debug[methodName] = tf
            if self.debug[methodName]:
                indent = " " * len(inspect.stack()) * 2
                print(indent, methodName, "*" * 30)
            return (methodName, indent, self.debug[methodName])
        
        def __init__(self, finishingSpeed, finishingAmount, finishingPass, finishingBottom, finishingNumPasses,
                    cutterDiameter, zStep, stepPercent, numSpringCuts, rapidHeight, speed):

            if finishingSpeed <= 0:
                raise Exception("ERROR Invalid finishing speed.")
            if finishingAmount < 0:
                raise Exception("ERROR finishing amount cannot be less than 0.0")
            if finishingNumPasses <= 0:
                raise Exception("ERROR finishing number passes must be >0")
            if cutterDiameter <= 0:
                raise Exception("ERROR cutter diameter must be greater than 0.0")
            if zStep >= 0:
                raise Exception("ERROR z step must be less than 0.0")
            if (stepPercent <= 0) or ((stepPercent > 1)):
                raise Exception("ERROR stepover percent must be greater than 0.0 and less than or equal to 1.0")
            if numSpringCuts < 0:
                raise Exception("ERROR number of spring cuts must be greater than or equal to 0")
            if speed <= 0:
                raise Exception("ERROR Invalid speed.")

            self.ss = []
            self.currentX = 0
            self.currentY = 0
            self.currentZ = 0
            self.oldSpeed = 20
            self.oldStepover = 0.5
            self.rapidSpeed = 40

            self.finishingSpeed = finishingSpeed
            self.finishingAmount = finishingAmount
            self.finishingPass = finishingPass
            self.finishingBottom = finishingBottom
            self.finishingNumPasses = finishingNumPasses
            self.cutterDiameter = cutterDiameter
            self.zStep = zStep
            self.stepPercent = stepPercent
            self.numSpringCuts = numSpringCuts
            self.RapidHeight = rapidHeight
            self.currentSpeed = speed

            self.fs = []
            self.EEE = 0.00001

            self.alphas = {}
            self.alphas["A"] = [[(0,0), (0,0.75), (0.5,1), (1,0.75), (1,0)], [(0,0.4), (1,0.4)]]
            self.alphas["B"] = [[(0,0), (0,1), (0.75,1), (1,0.9), (1,0.6), (0.75,0.5), (0,0.5), (0.75,0.5), (1,0.4), (1,0.1), (0.75,0), (0,0)]]
            self.alphas["C"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.1), (0.25,0), (0.75,0), (1,0.1)]]
            self.alphas["D"] = [[(0,0), (0,1), (0.75,1), (1,0.75), (1,0.25), (0.75,0), (0,0)]]
            self.alphas["E"] = [[(1,1), (0,1), (0,0.5), (0.5,0.5), (0,0.5), (0,0), (1,0)]]
            self.alphas["F"] = [[(1,1), (0,1), (0,0.5), (0.5,0.5), (0,0.5), (0,0)]]
            self.alphas["G"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.1), (0.25,0), (0.75,0), (1,0.1), (1,0.5), (0.5,0.5)]]
            self.alphas["H"] = [[(0,1), (0,0), (0,0.5), (1,0.5), (1,1), (1,0)]]
            self.alphas["I"] = [[(0.25,1), (0.75,1), (0.5,1), (0.5,0), (0.25,0), (0.75,0)]]
            self.alphas["J"] = [[(0.25,1), (0.75,1), (0.5,1), (0.5,0.2), (0.4,0), (0.1,0), (0,0.2)]]
            self.alphas["K"] = [[(0,1), (0,0), (0,0.5), (0.2,0.5), (1,1), (0.2,0.5), (1,0)]]
            self.alphas["L"] = [[(0,1), (0,0), (0.75,0)]]
            self.alphas["M"] = [[(0,0), (0,1), (0.5,0), (1,1), (1,0)]]
            self.alphas["N"] = [[(0,0), (0,1), (1,0), (1,1)]]
            self.alphas["O"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.1), (0.25,0), (0.75,0), (1,0.1), (1,0.9)]]
            self.alphas["P"] = [[(0,0), (0,1), (0.75,1), (1,0.9), (1,0.6), (0.75,0.5), (0,0.5)]]
            self.alphas["Q"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.1), (0.25,0), (0.75,0), (1,0.1), (1,0.9)], [(0.5,0.5), (1,0)]]
            self.alphas["R"] = [[(0,0), (0,1), (0.75,1), (1,0.9), (1,0.6), (0.75,0.5), (0,0.5), (0.5,0.5), (1,0)]]
            self.alphas["S"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.6), (0.25,0.5), (0.75,0.5), (1,0.4), (1,0.1), (0.75,0), (0.25,0), (0,0.1)]]
            self.alphas["T"] = [[(0,1), (1,1), (0.5,1), (0.5,0)]]
            self.alphas["U"] = [[(0,1), (0,0.1), (0.25,0), (0.75,0), (1,0.1), (1,1)]]
            self.alphas["V"] = [[(0,1), (0,0.5), (0.5,0), (1,0.5), (1,1)]]
            self.alphas["W"] = [[(0,1), (0,0.5), (0.25,0), (0.5,0.5), (0.75,0), (1,0.5), (1,1)]]
            self.alphas["X"] = [[(0,1), (1,0)], [(0,0),(1,1)]]
            self.alphas["Y"] = [[(0,1), (0.5,0.5), (1,1), (0.5,0.5), (0.5,0)]]
            self.alphas["Z"] = [[(0,1), (1,1), (0,0), (1,0)]]
            self.alphas["1"] = [[(0.25,0.75), (0.5,1), (0.5,1), (0.5,0), (0.25,0), (0.75,0)]]
            self.alphas["2"] = [[(0,0.9), (0.25,1), (0.75,1), (1,0.9), (1,0.6), (0.75,0.5), (0.25,0.5), (0,0.4), (0,0), (1,0)]]
            self.alphas["3"] = [[(0,0.9), (0.25,1), (0.75,1), (1,0.9), (1,0.6), (0.75,0.5), (0.25,0.5), (0.75,0.5), (1,0.4), (1,0.1), (0.75,0), (0.25,0), (0,0.1)]]
            self.alphas["4"] = [[(0.75,0), (0.75,1), (0,0.25), (1,0.25)]]
            self.alphas["5"] = [[(1,1), (0,1), (0,0.5), (0.25,0.6), (0.75,0.6), (1,0.5), (1,0.1), (0.75,0), (0.25,0), (0,0.1)]]
            self.alphas["6"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.1), (0.25,0), (0.75,0), (1,0.1), (1,0.5), (0.75,0.6), (0.25,0.6), (0,0.5)]]
            self.alphas["7"] = [[(0,1), (1,1), (0,0)]]
            self.alphas["8"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.6), (0.25,0.5), (0.75,0.5), (1,0.4), (1,0.1), (0.75,0), (0.25,0), (0,0.1), (0,0.4), (0.25,0.5), (0.75,0.5), (1,0.6), (1,0.9)]]
            self.alphas["9"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.6), (0.25,0.5), (0.75,0.5), (1,0.6), (1,0.9), (1,0.1), (0.75,0), (0.25,0), (0,0.1)]]
            self.alphas["0"] = [[(1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.1), (0.25,0), (0.75,0), (1,0.1), (1,0.9)], [(0,0), (1,1)]]
            self.alphas["!"] = [[(0.5,1), (0.5,0.35)], [(0.5,0)]]
            self.alphas["@"] = [[(0.75,0.35), (0.75,0.65), (0.5, 0.75), (0.35,0.65), (0.35,0.45), (0.6,0.35), (1,0.45), (1,0.9), (0.75,1), (0.25,1), (0,0.9), (0,0.1), (0.25,0), (0.75,0), (1,0.1)]]
            self.alphas["#"] = [[(0.33,1), (0.33,0)], [(0.66,0),(0.66,1)], [(1,0.66),(0,0.66)], [(0,0.33), (1,0.33)]]
            self.alphas["$"] = [[(1,0.8), (0.75,0.9), (0.25,0.9), (0,0.8), (0,0.6), (0.25,0.5), (0.75,0.5), (1,0.4), (1,0.2), (0.75,0.1), (0.25,0.1), (0,0.2)], [(0.5,0), (0.5,1)]]
            self.alphas["%"] = [[(0,0.9),(0.1,1),(0.2,1),(0.3,0.9),(0.3,0.8),(0.2,0.7),(0.1,0.7), (0,0.8), (0,0.9)], [(1,1), (0,0)], [(0.7,0.2),(0.8,0.3),(0.9,0.3),(1,0.2),(1,0.1),(0.9,0),(0.8,0), (0.7,0.1), (0.7,0.2)]]
            self.alphas["^"] = [[(0.25,0.5), (0.5,1), (0.75,0.5)]]
            self.alphas["&"] = [[(1,0), (0,0.7), (0,0.9), (0.25,1), (0.5,0.9), (0.5,0.7), (0,0.3), (0,0.1), (0.25,0), (0.5,0), (0.75,0.25)]]
            self.alphas["*"] = [[(0.5,1), (0.5,0)], [(0,0.75), (1,0.25)], [(1,0.75), (0,0.25)]]
            self.alphas["("] = [[(0.6,1), (0.4,0.75), (0.4,0.25), (0.6,0)]]
            self.alphas[")"] = [[(0.4,1), (0.6,0.75), (0.6,0.25), (0.4,0)]]
            self.alphas["~"] = [[(0,0.6), (0.25,0.8), (0.75,0.6), (1,0.8)]]
            self.alphas["`"] = [[(0,1), (0.25,0.75)]]
            self.alphas["_"] = [[(0,0), (1,0)]]
            self.alphas["-"] = [[(0.2,0.5), (0.8,0.5)]]
            self.alphas["+"] = [[(0.5,0.2), (0.5,0.8)], [(0.2,0.5), (0.8,0.5)]]
            self.alphas["="] = [[(0.2,0.75), (0.8,0.75)], [(0.2,0.25), (0.8,0.25)]]
            self.alphas["{"] = [[(0.6,1), (0.4,0.9), (0.4,0.6), (0.25,0.5), (0.4,0.4), (0.4,0.1), (0.6,0)]]
            self.alphas["}"] = [[(0.4,1), (0.6,0.9), (0.6,0.6), (0.75,0.5), (0.6,0.4), (0.6,0.1), (0.4,0)]]
            self.alphas["["] = [[(0.6,1), (0.4,1), (0.4,0), (0.6,0)]]
            self.alphas["]"] = [[(0.4,1), (0.6,1), (0.6,0), (0.4,0)]]
            self.alphas["|"] = [[(0.5,1), (0.5,0)]]
            self.alphas["\\"] = [[(0.25,1), (0.75,0)]]
            self.alphas[":"] = [[(0.5,0.75)], [(0.5,0.25)]]
            self.alphas[";"] = [[(0.5,0.75)], [(0.5,0.25), (0.3,0)]]
            self.alphas["\""] = [[(0.33,0.9), (0.33,0.6)], [(0.66,0.9), (0.66,0.6)]]
            self.alphas["'"] = [[(0.5,0.9), (0.5,0.6)]]
            self.alphas["<"] = [[(0.75,0.9), (0.25,0.5), (0.75,0.1)]]
            self.alphas[">"] = [[(0.25,0.9), (0.75,0.5), (0.25,0.1)]]
            self.alphas[","] = [[(0.5,0.25), (0.3,0)]]
            self.alphas["."] = [[(0.5,0)]]
            self.alphas["?"] = [[(0.1,0.9), (0.25,1), (0.75,1), (0.9,0.9), (0.9,0.7), (0.75,0.6), (0.5,0.4), (0.5,0.3)], [(0.5,0)]]
            self.alphas["/"] = [[(0.75,1), (0.25,0)]]
            self.alphas["a"] = [[(0.6,0.2), (0.25,0), (0.15,0), (0,0.15), (0,0.45), (0.15,0.6), (0.45,0.6), (0.6,0.45), (0.6,0.15), (0.6,0)]]
            self.alphas["b"] = [[(0,1), (0,0), (0,0.45), (0.15,0.6), (0.45,0.6), (0.6,0.45), (0.6,0.15), (0.45,0), (0.15,0)]]
            self.alphas["c"] = [[(0.6,0.6), (0.15,0.6), (0,0.45), (0,0.15), (0.15,0), (0.6,0)]]
            self.alphas["d"] = [[(0.6,0.6), (0.15,0.6), (0,0.45), (0,0.15), (0.15,0), (0.45,0), (0.6,0.15), (0.6,1), (0.6,0)]]
            self.alphas["e"] = [[(0,0.3), (0.6,0.3), (0.6,0.45), (0.6,0.6), (0.15,0.6), (0,0.45), (0,0.15), (0.15,0), (0.6,0)]]
            self.alphas["f"] = [[(0.75,1), (0.6,0.85), (0.6,0)], [(0.4,0.6), (0.75,0.6)]]
            self.alphas["g"] = [[(0.6,0.6), (0.15,0.6), (0,0.45), (0,0.15), (0.15,0), (0.6,0), (0.6,0.6), (0.6,-0.3), (0.45,-0.45), (0.15,-0.45)]]
            self.alphas["h"] = [[(0,1), (0,0), (0,0.45), (0.15,0.6), (0.45,0.6), (0.6,0.45), (0.6,0)]]
            self.alphas["i"] = [[(0.5,0), (0.5,0.5)], [(0.5,0.75)]]
            self.alphas["j"] = [[(0.5,0.75)], [(0.5,0.5), (0.5,-0.3), (0.45,-0.45), (0.15,-0.45)]]
            self.alphas["k"] = [[(0,1), (0,0), (0,0.3), (0.6,0.6), (0,0.3), (0.6,0)]]
            self.alphas["l"] = [[(0,1), (0,0.15), (0.15,0), (0.3,0)]]
            self.alphas["m"] = [[(0,0.6), (0,0), (0,0.45), (0.15,0.6), (0.3,0.6), (0.45,0.45), (0.45,0), (0.45,0.45), (0.6,0.6), (0.75,0.6), (0.9,0.45), (0.9,0)]]
            self.alphas["n"] = [[(0,0.6), (0,0), (0,0.45), (0.15,0.6), (0.3,0.6), (0.45,0.45), (0.45,0)]]
            self.alphas["o"] = [[(0.45,0.6), (0.15,0.6), (0,0.45), (0,0.15), (0.15,0), (0.45,0), (0.6,0.15), (0.6,0.45), (0.45,0.6)]]
            self.alphas["p"] = [[(0,0.6), (0,-0.4), (0,0), (0,0.45), (0.15,0.6), (0.45,0.6), (0.6,0.45), (0.6,0.15), (0.45,0), (0.15,0)]]
            self.alphas["q"] = [[(0.6,0.6), (0.15,0.6), (0,0.45), (0,0.15), (0.15,0), (0.6,0), (0.6,0.6), (0.6,-0.4)]]
            self.alphas["r"] = [[(0,0.6), (0,0), (0,0.45), (0.15,0.6), (0.3,0.6), (0.45,0.45)]]
            self.alphas["s"] = [[(0.6,0.6), (0.45,0.6), (0.15,0.6), (0, 0.45), (0.15,0.3), (0.45,0.3), (0.6,0.15),(0.45,0), (0,0)]]
            self.alphas["t"] = [[(0.5,1), (0.5,0)], [(0.3,0.6), (0.7,0.6)]]
            self.alphas["u"] = [[(0,0.6), (0,0.15), (0.15,0), (0.45,0), (0.6,0.15), (0.6,0.6)]]
            self.alphas["v"] = [[(0,0.6), (0.3,0), (0.6,0.6)]]
            self.alphas["w"] = [[(0,0.6), (0.25,0), (0.5,0.6), (0.75,0), (1,0.6)]]
            self.alphas["x"] = [[(0,0.6), (0.6,0)], [(0.6,0.6), (0,0)]]
            self.alphas["y"] = [[(0,0.6), (0,0.15), (0.15,0), (0.45,0), (0.6,0.15), (0.6,0.6), (0.6,-0.45), (0.15,-0.45)]]
            self.alphas["z"] = [[(0,0.6), (0.6,0.6), (0,0), (0.6,0)]]
            self.Mgk = ImageMagick()

            self.debug = {}

#START_COVERAGE#

        #********************************************************************
        # Draws multiple polys on an image
        #********************************************************************
        def DrawPolys(self, cutterDiameter, l, minX, minY, maxX, maxY, fillNonZero):        
            # Image resolution is 1/32 of cutter diameter
            res = cutterDiameter / 32

            # Create image from min to max coordinates with border
            width = ((maxX - minX) + res) + 2 * res
            height = ((maxY - minY) + res) + 2 * res
            cols = (int)(width / res)
            rows = (int)(height / res)
            minVec = (minX,minY)
            borderVec = (res,res)

            # Draw and fill the polys
            
            im = numpy.zeros((rows,cols))
            for ll in l:
#                Blender4CNC.PolytoxogonDraw.GetPathForDrawPolyNoMagic(ll, minVec, borderVec, res, im)
                self.GetPathForDrawPolyNoMagic(ll, minVec, borderVec, res, im)
            return (rows,cols,res,im)
        
        def GetPathForDrawPolyNoMagic(self, poly1, minVec, borderVec, res, im):        
            #print("GetPathForDrawPolyNoMagic poly1, minVec, borderVec, res, im=", poly1, minVec, borderVec, res, im)
            s = []
            roughPoints = poly1.points
            #print("GetPathForDrawPolyNoMagic poly1.points=", poly1.points)

            # This function does not get called for circular pockets
            #if self.IsACircle(poly1):
            #    P1 = roughPoints[0]   
            #    P1 = ((P1[0], P1[1]) - minVec + borderVec) / res 
            #    # Get Center Point
            #    p = roughPoints[1]
            #    C = ((p[2], p[3]) - minVec + borderVec) / res # center
            #    # Get vector from start point to center
            #    vx = C[0] - P1[0]
            #    vy = C[1] - P1[1]
            #    m = sqrt(vx**2 + vy**2)
            #    r = m
            #    # fill circle
            #    rr, cc = skimage.draw.circle(C[0], C[1], r, im.shape)
            #    im[cc, rr] = 255
            #    return 

            r = []
            c = []
            for i in range(0,len(roughPoints)):
                P1 = roughPoints[i-1]   
                P1x = (P1[0] - minVec[0] + borderVec[0]) / res
                P1y = (P1[1] - minVec[1] + borderVec[1]) / res
                P1 = (P1x, P1y)
                if i == 0: # Move to start of poly
                    r.append(P1[0])
                    c.append(P1[1])
                p = roughPoints[i]
                P2x = (p[0] - minVec[0] + borderVec[0]) / res
                P2y = (p[1] - minVec[1] + borderVec[1]) / res
                P2 = (P2x, P2y)
                
                if Blender4CNC.Polytoxogon.PointIsStraight(p,p): # Line from P1 to P2
                    r.append(P2[0])
                    c.append(P2[1])
                    
                else: # Curve from P1 to P2 center C
                    # Approximate the curve
                    Cx = (p[2] - minVec[0] + borderVec[0]) / res
                    Cy = (p[3] - minVec[1] + borderVec[1]) / res
                    C = (Cx, Cy)

#                    ang1 = Blender4CNC.PolytoxogonDraw.GetAngle0to360CenterToPoint(C, P1)
#                    ang2 = Blender4CNC.PolytoxogonDraw.GetAngle0to360CenterToPoint(C, P2)
                    ang1 = self.GetAngle0to360CenterToPoint(C, P1)
                    ang2 = self.GetAngle0to360CenterToPoint(C, P2)

                    vx = P2[0] - C[0]
                    vy = P2[1] - C[1]
                    m = sqrt(vx**2 + vy**2)
                    radius = m    # radius
                    oneRadian = (1 / 180) * math.pi
                    
                    ang = ang1
#                    if Blender4CNC.PolytoxogonDraw.IsClockwise(p): 
                    if self.IsClockwise(p): 
                        if ang2 > ang1:
                            # Go clockwise from ang1 to 0
                            while ang > 0:
                                r.append(C[0] + (math.cos(ang * math.pi / 180) * radius))
                                c.append(C[1] + (math.sin(ang * math.pi / 180) * radius))   
                                ang -= 1
                            ang += 360
                        # Go clockwise from ang to ang2
                        while ang > ang2:
                            r.append(C[0] + (math.cos(ang * math.pi / 180) * radius))
                            c.append(C[1] + (math.sin(ang * math.pi / 180) * radius))   
                            ang -= 1
                    else: 
                        if ang2 < ang1:
                            # Go counter-clockwise from ang1 to 0
                            while ang < 360:
                                r.append(C[0] + (math.cos(ang * math.pi / 180) * radius))
                                c.append(C[1] + (math.sin(ang * math.pi / 180) * radius))   
                                ang += 1
                            ang -= 360
                        # Go counter-clockwise from ang to ang2
                        while ang < ang2:
                            r.append(C[0] + (math.cos(ang * math.pi / 180) * radius))
                            c.append(C[1] + (math.sin(ang * math.pi / 180) * radius))   
                            ang += 1
            r = numpy.array(r)
            c = numpy.array(c)
            rr, cc = skimage.draw.polygon(r, c)
            im[cc, rr] = 255
#            print("im.shape=", im.shape)
##            if im.shape == (45,45):
#            if True:
#                print("[")
#                for ir in range(0,im.shape[1]):
#                    print("[", end="")
#                    for ic in range(0,im.shape[0]-1):
#                        print(str(int(im[ic,ir])) + ",", end="")
#                    print(int(im[im.shape[0]-1,ir]), end="")
#                    if ir != im.shape[0]-1:
#                        print("],")
#                    else:
#                        print("]")
#                print("]")
                
            return s

        #********************************************************************
        # Return true if this Polytoxogon is a circle
        #********************************************************************
        def IsACircle(self, poly1):
            # They are a 2-point list consisting of start point and arc command around 360 deg.
            if len(poly1.points) == 2:
                (p1, p2) = poly1.points
                FEQ = Blender4CNC.FloatsAreEqual
                if FEQ(p1[0], p2[0]) and FEQ(p1[1], p2[1]):
                    # FAILS COVERAGE
                    return (poly1.PointIsStraight(p1) != poly1.PointIsStraight(p2))
            return False

        #********************************************************************
        # Returns the angle in degrees that the vector from C to P1 makes 
        # with respect to 0 (East)
        #********************************************************************
        def GetAngle0to360CenterToPoint(self, C, P1):
            x = P1[0] - C[0]
            y = P1[1] - C[1]
            ang1 = Blender4CNC.Util2d.angle_signed((x,y), (1,0))
            if ang1 < 0:
                ang1 = -ang1
            if y < 0:
                ang1 = 2 * math.pi - ang1
            ang1 = (ang1 / math.pi) * 180
            return ang1

        #********************************************************************
        # Returns True if point is a clockwise curve
        #********************************************************************
        def IsClockwise(self, p):
            return p[4] == 1
                
        #********************************************************************
        # Returns difference between two angles
        #********************************************************************
        def DiffAngle(self, ang1, ang2):
            if (ang1 > ang2):
                return ang1 - ang2
            else:
                return (360 - ang2) + ang1

        #******************************************************************************
        # Returns a point mirrored around the X=0 axis
        #******************************************************************************
        def FlipX(self,p):
            return (-p[0], p[1]) 

        #******************************************************************************
        # Given a list of coordinates (lines or curves) will translate all points by
        # "origin"
        #******************************************************************************
        def Translate(self,l,origin):
            l2 = []
            for i in range(0,len(l)):
                if (len(l[i]) == 2):
                    l2 += [ (l[i][0]+origin[0], l[i][1]+origin[1]) ]
                else:
                    l2 += [ (l[i][0]+origin[0], l[i][1]+origin[1], l[i][2]+origin[0], l[i][3]+origin[1], l[i][4]) ]
            return l2
            
        #******************************************************************************
        # Given magnitude and angle in degrees, returns an X,Y vector
        #******************************************************************************
        def PolarDegrees(self,mag,angle):
            ang = (angle / 180) * math.pi
            x = mag * cos(ang)
            y = mag * sin(ang)
            prec = 15
            x = round(x, prec)
            y = round(y, prec)
            return (x,y)

        #********************************************************************
        # Finish the CNC GCode program - always call this function at the end
        #********************************************************************
        def EndProgram(self):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            self.ss += self.EndProgramStringList()
            self.ss.append("( Total Lines = %d )" % (len(self.ss)+1))
            #print("Finished %d Lines of GCode" % (len(self.ss)+1))

        #********************************************************************
        # Initialize the CNC GCode program - always call this function first!
        #********************************************************************
        def InitProgram(self, speed, gcodePreAmble):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            self.ss = self.InitProgramStringList(gcodePreAmble)
            self.ss += self.IntSpeed(speed)

        #********************************************************************
        # 
        #********************************************************************
        def InsertGCode(self, l):
            self.ss += l

        #********************************************************************
        # Select a numbered tool
        #********************************************************************
        def SelectTool(self, tool):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            self.ss += ["T%d" % tool, "M6"]

        #********************************************************************
        # Set the current feed speed
        #********************************************************************
        def Speed(self, spd):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            self.ss += self.IntSpeed(spd)

        #********************************************************************
        def GetSpeedGCodeStr(self, spd):
            return "F%.4f" % spd

        #********************************************************************
        # (Trajectory blending allows the control software to deviate from
        # the exact path to maintain machine tool velocity. Disabling it
        # makes it accurately follow the path.)
        #********************************************************************

        #********************************************************************
        # Disable trajectory blending.
        #********************************************************************
        def DisableTrajectoryBlending(self):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            self.ss += self.IntDisableTrajectoryBlending()

        #********************************************************************
        # Enable DEFAULT trajectory blending.
        #********************************************************************
        def EnableDefaultTrajectoryBlending(self):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            self.ss += ["G64 (Enable default Trajectory Blending)"]

        #********************************************************************
        # Pause the program and wait for user to click OK
        #********************************************************************
        def Pause(self, msg):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            self.ss.append("M0 (%s)" % msg)

        #********************************************************************
        # Cut a circular pocket of radius at x,y starting at depth=z1 down to
        # depth=z2
        # It uses the current settings for:
        #   cutter diameter
        #   Z Step
        #   StepOver Percent
        #   Number Spring Cuts
        # If finishing is enabled it will do a finishing pass with the finishing 
        # parameters.
        #********************************************************************
        def CutCircularPocket(self,x,y,radius,z1,z2, finishingPass):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            if finishingPass:
                fs = self.IntCutCircularPocket(x,y,radius-self.finishingAmount,z1,z2+self.finishingAmount)
                # Cut the finishing pass                
                fs = fs[0:-1] # Remove end rapid to safe Z
                fs += self.IntStartFinishing(self.finishingSpeed / self.currentSpeed)
                fs += self.IntFinishCircularPocket(x,y,radius,z1,z2)
                fs += self.IntCutCircularPocket(x,y,radius,z2+self.finishingAmount,z2)
                fs += self.IntEndFinishing()
            else:
                fs = self.IntCutCircularPocket(x,y,radius,z1,z2)
            return fs

        #********************************************************************
        # Cut on center line of a circle of radius at x,y starting at depth z1
        # down to depth=z2.
        # It uses the current settings for:
        #   Z Step
        #********************************************************************
        def CutCircle(self,x,y,radius,z1,z2):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            if z1 < z2:
                raise("ERROR z1 must be greater than or equal to z2")
            fs = self.IntCutCircle(x,y,radius,z1,z2)
            return fs


        #********************************************************************
        # Cut a poly pocket from a list of points (vectors) starting 
        # at depth=z1 down to depth=z2. It handles a list of tenons (mountains
        # within the pocket) that represent material to be left standing.
        # If finishing is enabled it will do a finishing pass with the finishing 
        # parameters.
        #********************************************************************
        def CutPocket(self,listOfXYPoints,z1,z2,trim,tenons=None):
            return self.CutPocketRoughFinal(listOfXYPoints,z1,z2,trim,self.cutterDiameter,self.finishingPass,self.finishingBottom,self.finishingAmount, self.stepPercent, self.RapidHeight, self.finishingNumPasses,tenons,False)

        #********************************************************************
        def CutPocketNoRough(self,listOfXYPoints,z1,z2,trim,tenons=None):
            return self.CutPocketRoughFinal(listOfXYPoints,z1,z2,trim,self.cutterDiameter,self.finishingPass,self.finishingBottom,self.finishingAmount, self.stepPercent, self.RapidHeight, self.finishingNumPasses,tenons,True)

        #********************************************************************
        def ShrinkAndCatchSplitting(self, finalPoly, shrinkAmount):
            try:
                finishPolyList = finalPoly.Shrink(shrinkAmount)
                if len(finishPolyList) > 1:
                    raise Blender4CNC.PolyException("Shape is split.", mainPoly.points[0])
                return finishPolyList[0]
            except Blender4CNC.PolyException as err:
                str2 = err.args[0] + "\nThis error means that the cutter cannot\nreach all areas of the pocket safely due to the cutter\nradius or the finish/trim amounts.\n"
                raise Blender4CNC.PolyException(str2, err.args[1])
        #********************************************************************
        def AnyTenonsCompletelyInsideAnotherTenon(self, finalTenonsList):
            for i in range(0,len(finalTenonsList)):
                poly1 = finalTenonsList[i]
                for j in range(i+1,len(finalTenonsList)):
                    poly2 = finalTenonsList[j]
                    (poly1IsSame, poly1IsInside, poly1Touches, poly1IsOutside) = poly2.SameInsideOutside(poly1)
                    if poly1IsSame or poly1IsInside:
                        return True
                    (poly2IsSame, poly2IsInside, poly2Touches, poly2IsOutside) = poly1.SameInsideOutside(poly2)
                    if poly2IsSame or poly2IsInside:
                        return True
            return False
        #********************************************************************
        # The shape of the pocket must be shrunk to account for cutter radius
        # and any finish or trim amount. When shrunk by the respective amounts,
        # the pocket is not allowed to have areas "choked off" - this is an error.
        #
        # Likewise, if there are any tenons, the tenons cannot overlap, nor
        # can the resulting tenon shapes overlap when accounting for cutter
        # radius or finish/trim amounts - this is an error.
        #********************************************************************
        def CutPocketRoughFinal(self,listOfXYPoints, z1,z2,trim, cutterDiameter,finishingPass,finishingBottom,finishingAmount, stepPercent, RapidHeight, finishingNumPasses, tenons,finalOnly):
            trim = max(trim,0)
            radius = cutterDiameter/2

            # Adjust z2 based on finishing
            origZ2 = z2
            if finishingPass and finishingBottom:
                z2 = z2 + finishingAmount

            mainPoly = Blender4CNC.Polytoxogon(listOfXYPoints)
            (minX, minY, maxX, maxY) = mainPoly.GetBoundingRectangle()

            # Draw the pocket as final size
#            (rows,cols,res, imFinalSize) = Blender4CNC.PolytoxogonDraw.DrawPolys(cutterDiameter, [mainPoly], minX, minY, maxX, maxY, False) 
            (rows,cols,res, imFinalSize) = self.DrawPolys(cutterDiameter, [mainPoly], minX, minY, maxX, maxY, False) 
            mainPoly.IsValid()

            # Determine whether we are doing a climb cut or not
            climbCut = False
            if not mainPoly.PolyIsClockwise():
                climbCut = True
                mainPoly = mainPoly.ReverseLineDirections()
            
            finalPoly = self.ShrinkAndCatchSplitting(mainPoly, radius)
            # If doing a finishing pass, shrink the main poly by the finishing amount
            if finishingPass:
                finishPoly = self.ShrinkAndCatchSplitting(finalPoly, finishingAmount)
            else:
                finishPoly = finalPoly

            # If doing a trim pass, shrink the main poly by the trim amount
            if trim > 0:
                trimPoly = self.ShrinkAndCatchSplitting(finishPoly, trim)
            else:
                trimPoly = finishPoly

            # Process any tenons
            finalTenonsList = []
            finishTenonsList = []
            trimTenonsList = []
            climbCutTenons = []
            if isinstance(tenons, list) and (len(tenons) > 0):
                # Create a list of polys for the tenons
                polyListPre = [Blender4CNC.Polytoxogon(t) for t in tenons]
                # Check that the tenon polys are valid
                for i in range(0,len(polyListPre)):
                    poly1 = polyListPre[i]
                    # Determine whether we are doing a climb cut or not
                    if not poly1.PolyIsClockwise():
                        poly2 = poly1.ReverseLineDirections()
                        #poly2.CheckIsGood()
                        poly2.IsValid()
                        # This is not possible
                        #if not poly2.PolyIsClockwise():
                        #    raise Blender4CNC.PolyException("ERROR - poly is not clockwise!", poly2.points[0][0:2])
                        climbCutTenons.append(True)
                        polyListPre[i] = poly2
                    else:
                        #poly1.CheckIsGood()
                        poly1.IsValid()
                        climbCutTenons.append(False)
                
                # Throw out any tenons that are completely inside another tenon
                polyListPre2 = []
                climbCutTenons2 = []
                for i in range(0,len(polyListPre)):
                    poly1 = polyListPre[i]
                    foundInside = False
                    for j in range(0,len(polyListPre)):
                        if i==j:
                            continue
                        poly2 = polyListPre[j]
                        (poly1IsSame, poly1IsInside, poly1Touches, poly1IsOutside) = poly2.SameInsideOutside(poly1)
                        if poly1IsSame or poly1IsInside:
                            foundInside = True
                            break
                    if not foundInside:
                        polyListPre2.append(poly1)
                        climbCutTenons2.append(climbCutTenons[i])
                polyListPre = polyListPre2
                climbCutTenons = climbCutTenons2
                    
                # Join overlapping tenons
                tenonsList = self.JoinOverlappingTenons(polyListPre)
                if len(tenonsList) != len(polyListPre):
                    str2 = "Detected overlapping tenons.\n"
                    raise Blender4CNC.PolyException(str2, (0,0))
                
                # Expand all the polys by the cutter radius
                finalTenonsList = mainPoly.ExpandPolys(tenonsList, radius)
                finalTenonsList = [item[0] for item in finalTenonsList]
                # Join overlapping tenons
                finalTenonsList = self.JoinOverlappingTenons(finalTenonsList)
                if len(finalTenonsList) != len(tenonsList):
                    str2 = "Detected overlapping tenons.\nThe cutter is too large to safely pass between tenons."
                    raise Blender4CNC.PolyException(str2, (0,0))
                #print("CutPocket finalTenonsList=", finalTenonsList)
                
                # If doing a finishing pass, expand the polys by the finishing amount
                if finishingPass:
                    #print("CutPocket Do finish pass")
                    finishTenonsList = mainPoly.ExpandPolys(finalTenonsList, finishingAmount)
                    finishTenonsList = [item[0] for item in finishTenonsList]
                    # Join overlapping tenons
                    finishTenonsList = self.JoinOverlappingTenons(finishTenonsList)
                    if len(finishTenonsList) != len(finalTenonsList):
                        str2 = "Detected overlapping tenons.\nThe cutter is too large to safely pass between tenons\nwhen accounting for the finish amount."
                        raise Blender4CNC.PolyException(str2, (0,0))
                else:
                    finishTenonsList = finalTenonsList
                    #print("CutPocket NO finish pass")

                # If doing a trim pass, expand the polys by the trim amount
                if trim > 0:
                    #print("CutPocket Do trim pass")
                    trimTenonsList = mainPoly.ExpandPolys(finishTenonsList, trim)
                    trimTenonsList = [item[0] for item in trimTenonsList]
                    # Join overlapping tenons
                    trimTenonsList = self.JoinOverlappingTenons(trimTenonsList)
                    if len(trimTenonsList) != len(finishTenonsList):
                        str2 = "Detected overlapping tenons.\nThe cutter is too large to safely pass between tenons\nwhen accounting for the finish and trim amount."
                        raise Blender4CNC.PolyException(str2, (0,0))
                else:
                    trimTenonsList = finishTenonsList
                    #print("CutPocket NO trim pass")

                # After expanding, the tenons may overlap with the edge of the pocket
                strA = "Tenons overlap pocket edge.\nThe cutter is too large to safely pass between tenons and pocket edge."
                (finalPoly2, finalTenonsList2) = finalPoly.SubtractEdgeTenonsFromPoly(finalPoly, finalTenonsList)
                if len(finalTenonsList2) != len(finalTenonsList):
                    raise Blender4CNC.PolyException(strA, (0,0))
                (finishPoly2, finishTenonsList2) = finalPoly.SubtractEdgeTenonsFromPoly(finishPoly, finishTenonsList)
                if len(finishTenonsList2) != len(finishTenonsList):
                    raise Blender4CNC.PolyException(strA + "\nwhen accounting for finish amount.", (0,0))
                (trimPoly2, trimTenonsList2) = finalPoly.SubtractEdgeTenonsFromPoly(trimPoly, trimTenonsList)
                if len(trimTenonsList2) != len(trimTenonsList):
                    raise Blender4CNC.PolyException(strA + "when accounting for trim amount.", (0,0))
                finalTenonsList = finalTenonsList2
                finishTenonsList = finishTenonsList2
                trimTenonsList = trimTenonsList2

                # Must check that none of the tenons are equal or larger than the pocket poly
                for tenon in finalTenonsList:
                    (poly2IsSame, poly2IsInside, poly2Touches, poly2IsOutside) = finalPoly.SameInsideOutside(tenon)
                    if poly2IsSame or poly2IsOutside:
                        # There is nothing to do - the tenon dwarfs the poly!
                        str2 = "A tenon is larger than the size of the pocket."
                        raise Blender4CNC.PolyException(str2, (0,0))
                # Checking for a finish tenon that dwarfs the poly is handled above when we "subtract" the 
                # tenons from the main poly (we get an empty list which triggers an exception)

                # Checking for a trim tenon that dwarfs the poly is handled above when we "subtract" the 
                # tenons from the main poly (we get an empty list which triggers an exception)

                # If we have any tenons (final, finish, or trim) that are completely inside another
                # tenon then that means that the larger tenon has merged around with itself and
                # enclosed a section of the pocket - this is an error as it does not allow us to 
                # achieve the desired accuracy
                # Raise an exception in AnyTenonsCompletelyInsideAnotherTenon function
                strA = "A tenon shape curves around to meet itself.\nThe cutter radius "
                strB = " is too large to reach\ninto the internal area of a tenon."
                if self.AnyTenonsCompletelyInsideAnotherTenon(finalTenonsList):
                    raise Blender4CNC.PolyException(strA + strB, (0,0))
                # If any the finish or trim tenons are completely inside another tenon,
                # then the final tenon will also be inside another final tenon
                # So testing the finishTenonsList and trimTenonsList is covered already
                #if self.AnyTenonsCompletelyInsideAnotherTenon(finishTenonsList):
                #    raise Blender4CNC.PolyException(strA + "and finish amount" + strB, (0,0))
                #if self.AnyTenonsCompletelyInsideAnotherTenon(trimTenonsList):
                #    raise Blender4CNC.PolyException(strA + "and finish and trim amount" + strB, (0,0))

            # At this point, we have 3 polys for the pocket edge - finalPoly, finishPoly and trimPoly
            # At this point, we have 3 poly lists for the tenons - finalTenonsList, finishTenonsList and trimTenonsList
            # (Tenons lists may be empty)   

            # Draw the final shape pass
            # The DrawPolys function makes it so that a pixel represents (cutterDiameter/32) inches
            # - this is the "resolution" (the 'res' variable returned)
            # i.e. if the cutter is 0.25", then 0.25/32 = 0.0078125"
            # therefore the radius of the cutter in pixels is (cutterDiameter/2) / res
            # i.e for 0.25" cutter, the radius is equal to 16 pixels (0.125" / 0.0078125")
#            (rows,cols,res, imFinalShape) = Blender4CNC.PolytoxogonDraw.DrawPolys(cutterDiameter, [trimPoly], minX, minY, maxX, maxY, False)
            if climbCut:
                # While it may not really make any difference to drawing the shape onto an image
                # We are going to try and be exact here
                tempPoly = trimPoly.ReverseLineDirections()
                (rows,cols,res, imFinalShape) = self.DrawPolys(cutterDiameter, [tempPoly], minX, minY, maxX, maxY, False)
            else:
                (rows,cols,res, imFinalShape) = self.DrawPolys(cutterDiameter, [trimPoly], minX, minY, maxX, maxY, False)

            if len(finalTenonsList) != 0: 
#                (rT,cT,rT, imTenons) = Blender4CNC.PolytoxogonDraw.DrawPolys(cutterDiameter, trimTenonsList, minX, minY, maxX, maxY, True)
                (rT,cT,rT, imTenons) = self.DrawPolys(cutterDiameter, trimTenonsList, minX, minY, maxX, maxY, True)

                # Subtract 2 images
                imC = imFinalShape - imTenons
                imD = numpy.where(imC<0, 0, imC)

                #im2g.Mgk = ImageMagick()
                # Make the image just 0 and 1 for black/white
                imD = imD / 255
                imFinalShape = imD

            imA = imFinalShape

            # Erode the final shape to see if there are any pixels left for roughing
            # Instead of eroding by half the diameter of the bit, just erode by a small amount
            #radius = cutterDiameter/2
            #cutterRadiusPixelsFloat = radius / res
            #cutterRadiusPixels = int(radius / res)
            #if cutterRadiusPixelsFloat > cutterRadiusPixels:
            #    cutterRadiusPixels += 1
            sizeK = 5
            k = self.GetDiscKernel(sizeK)
            imB = copy.copy(imA)
            scipy.ndimage.morphology.binary_erosion(imA, structure=k, output=imB)
            imB *= 255
            im = imB
            needRough = (numpy.count_nonzero(im) > 0)

            # We use Im2GCode for functions: HandleRingStructures, GetGCodeForThisBlob
            #     GetGCodeForThisBlob calls FillBlob, GetGCodeForPoint, GetX
            im2g = Blender4CNC.Im2GCode()
            im2g.listOfDepths = [0]     # Used by HandleRingStructures
            im2g.rows = rows-2          # Used by HandleRingStructures, GetGCodeForThisBlob
            im2g.cols = cols-2          # Used by HandleRingStructures, GetGCodeForThisBlob
            im2g.lastX = 0              # Used by GetGCodeForPoint
            im2g.lastY = 0              # Used by GetGCodeForPoint
            im2g.lastZ = 0              # Used by GetGCodeForPoint
            im2g.pixelInInches = cutterDiameter / 32 # Used by GetX
            im2g.innerPathToleranceEnableCount = 0 # Used by GetGCodeForThisBlob
            im2g.bgnd = 0               # Used by FillBlob
            i2g = Blender4CNC.Im2GCodeSettings()
            i2g.offset_x = 0            # Used by GetX
            i2g.offset_y = 0            # Used by GetX
            im2g.i2g = i2g
            
            # Handle ring structures after the erosion
            imB /= 255
            imA = im2g.HandleRingStructures(imB)
            imFinalShape = imA

            fs = []
            roughPath = []
            # Rough out the pocket
            if needRough:

                # A Chebyshev (chessboard) distance transform
                #imA = im
                imB = self.DISTANCE(imA)
                #Blender4CNC.GrayImages.SaveGrayPNG("CutPocketRoughFinal-distance.png", imB)

                # Load in the image
                filename = "CutPocketADist.png"
                im = imB
                
                # Reshape to 3D
                im = im.reshape((1, rows, cols))

                # The eroding/thinning might have left us with multiple blobs
                DEBUG_counter = 1
                while True:
                    # Find first point
                    wh = numpy.where(im==1)
                    if (not wh) or (len(wh[0]) == 0): # if the arrays in wh are not initialized, nothing was found
                        break

#                    # Temporary for debugging
#                    temp = im[0, wh[2][0], wh[1][0]]
#                    im[0, wh[2][0], wh[1][0]] = 255
#                    im = im.reshape((rows, cols))
#                    Blender4CNC.GrayImages.SaveGrayPNG("CutPocketRoughFinal-255-start.png", im)
#                    im = im.reshape((1, rows, cols))
#                    im[0, wh[2][0], wh[1][0]] = temp
#                    # Temporary for debugging
                    
                    firstPixel = Blender4CNC.MyPix(wh[2][0], wh[1][0], 1, 0)
                    # Get the path to cut this at this level
                    # Shrink the step percent to make sure we get good coverage
                    modulus = ((cutterDiameter * stepPercent * 0.9) / res) 
                    path = im2g.GetGCodeForThisBlob(im, modulus, 0, firstPixel)
                    #print("im2g.GetGCodeForThisBlob")
                    #print(wh[2][0], wh[1][0])
                    #print("path=", path)
                    #print("")


                    # If "finalOnly" is True it means we are doing the roughing with a larger cutter
                    # and we only need to do a few outside loops here at this cutter size
                    if finalOnly:
                        path = self.JustGetAFewLoops(path)

                    # Slow down the speed as we move into inner loops because we are removing 100%
                    # of the material
                    path = self.SlowDownGoingIn(path)

                    # Translate origin
                    fs += ["\n"]
                    fs += ["(Roughing the Pocket)\n"]
                    # Cut the polys
                    #print("AddOffsetToPath minX, minY=", minX, minY)
                    if (bpy.context.scene.unit_settings.system == "METRIC"):
                        offsetPath = self.AddOffsetToPath(path, minX * 1000, minY * 1000)
                    else:
                        offsetPath = self.AddOffsetToPath(path, minX, minY)
                    fs += self.CutPathFromZ1ToZ2(offsetPath, offsetPath, z1, z2)
                    roughPath = path

                    fs += self.RapidToZ(RapidHeight)
                    # Translate origin back

                    # Clear this blob from the image
                    self.ClearBlob(im, wh[2][0], wh[1][0])
                    
                fs += ["(Finished Roughing the Pocket)\n"]
                fs += ["\n"]
            # End if

            # The roughing pass can enable trajectory blending so we want to make sure
            # it is disabled!
            fs += ["\n"]
            fs += self.IntDisableTrajectoryBlending()

            # At this point, the pocket area has been roughed (with trajectory blending) 
            # If we have enabled "finishBottom" then the current z2 depth is "finishAmount"
            # ABOVE the final z2 depth
            
            # If we are finishing the bottom, then adjust z2 and repeat the above for roughing
            z2 = origZ2
            fs += ["\n"]
            fs += ["(Finishing the Pocket)\n"]
            fs += self.IntStartFinishing(0)
            
            if finishingPass and finishingBottom:
                if len(roughPath) > 0:
                    # Translate origin, Cut the polys
                    fs += ["(Finishing the Pocket - the bottom surface)\n"]
                    if (bpy.context.scene.unit_settings.system == "METRIC"):
                        offsetPath = self.AddOffsetToPath(roughPath, minX * 1000, minY * 1000)
                    else:
                        offsetPath = self.AddOffsetToPath(roughPath, minX, minY)
                    fs += self.CutPathFromZ1ToZ2(offsetPath, offsetPath, z2, z2)
                    fs += self.RapidToZ(RapidHeight)
                else:
                    fs += ["(Nothing to do for bottom surface area)\n"]
            else:
                fs += ["(bottomFinishing = False)\n"]

            # The roughing pass can enable trajectory blending so we want to make sure
            # it is disabled!
            fs += ["\n"]
            fs += self.IntDisableTrajectoryBlending()

            # Now cut the trim perimeter 
            if trimPoly != finishPoly:
                # Check if any tenons are climb cut and need to be reversed
                for i in range(0,len(climbCutTenons)):
                    if climbCutTenons[i]:
                        trimTenonsList[i] = trimTenonsList[i].ReverseLineDirections()
                fs += self.IntCutPocket_Perimeter("(Trimming Pocket)\n", "(Finished Trimming Pocket)\n", "(Trimming Tenons)\n", "(Finished Trimming Tenons)\n", trimPoly, climbCut, z1, z2, (trimTenonsList != finishTenonsList), trimTenonsList)

            # Now cut the finish perimeter 
            if finishPoly != finalPoly:
                # Check if any tenons are climb cut and need to be reversed
                for i in range(0,len(climbCutTenons)):
                    if climbCutTenons[i]:
                        finishTenonsList[i] = finishTenonsList[i].ReverseLineDirections()
                fs += self.IntCutPocket_Perimeter("(Pre-finish pass of Pocket)\n", "(Finished Pre-finish pass of Pocket)\n", "(Pre-finish pass of the Tenons)\n", "(Finished Pre-finish pass of the Tenons)\n", finishPoly, climbCut, z1, z2, (finishTenonsList != finalTenonsList), finishTenonsList)

            # Now cut the final perimeter 
            fs += ["\n"]
            fs += ["(Cutting Final Perimeter of the Pocket)\n"]
            fs += ["(%d passes)\n" % finishingNumPasses]

            # Make sure to disable trajectory blending!
            fs += self.IntDisableTrajectoryBlending()


            if climbCut:
                # Must go opposite direction for climb cut (CCW)
                finalPoly2 = finalPoly.ReverseLineDirections()
                finalPoints = finalPoly2.points
            else:
                finalPoints = finalPoly.points
            path = self.IntPointsToPath(finalPoints,1)
            for numPass in range(0, finishingNumPasses):
                fs += self.CutPathFromZ1ToZ2(path, path, z1, z2)
                fs += self.RapidToZ(RapidHeight)
            fs += ["(Finished Cutting Final Perimeter of the Pocket)\n"]
            fs += ["\n"]
            
            if len(finalTenonsList) > 0:
                fs += ["(Cutting Final of the Tenons)\n"]
                # Check if any tenons are climb cut and need to be reversed
                for i in range(0,len(climbCutTenons)):
                    if climbCutTenons[i]:
                        finalTenonsList[i] = finalTenonsList[i].ReverseLineDirections()
                fs += self.CutAccuratePathList(finalTenonsList, z1, z2)
                fs += ["(Finished Cutting Final of the Tenons)\n"]
                fs += ["\n"]
            fs += self.IntEndFinishing()
            fs += ["(Pocket Complete)\n"]
            fs += ["\n"]
            return fs

        def IntCutPocket_Perimeter(self,msgA, msgB, msgC, msgD, poly, climbCut, z1, z2, doTenons, tenonsList):
            fs = ["\n", msgA]
            if climbCut:
                # Must go opposite direction for climb cut (CCW)
                poly2 = poly.ReverseLineDirections()
                fs += self.CutAccuratePath(poly2.points, z1, z2)
            else:
                fs += self.CutAccuratePath(poly.points, z1, z2)
            fs += [msgB, "\n"]
            if doTenons:
                fs += [msgC]
                fs += self.CutAccuratePathList(tenonsList, z1, z2)
                fs += [msgD, "\n"]
            return fs

        def DISTANCE(self, im):
            return scipy.ndimage.morphology.distance_transform_cdt(im, metric='chessboard', return_distances=True)

        #*************************************************************************
        # Create a disc kernel to be used with binary dilation
        #*************************************************************************
        def GetDiscKernel(self, radius):
            # Generate a quarter
            r = ceil(radius) + 1
            r2 = radius**2
            k = numpy.zeros((r,r))
            for x in range(0,r):
                for y in range(0,r):
                    d = x**2 + y**2
                    if d <= r2:
                        k[x,y] = 1
            # Mirror to create half
            k2 = k[1:,]
            k2 = numpy.flip(k2,0)
            k2 = numpy.vstack((k2,k))
            # Mirror to create whole
            k3 = k2[:,1:]
            k3 = numpy.flip(k3,1)
            k3 = numpy.hstack((k3,k2))
            # If nothing in outer band, reduce array to save computations
            sz = r * 2 - 1
            if sum(k3[0,:]) == 0:
                # FAILS COVERAGE
                k3 = k3[1:sz-1,1:sz-1]
            return k3
        # End GetKernel

        #********************************************************************
        # For a list of tenon polys, determine if any overlap. Join those
        # polys that overlap
        #********************************************************************
        def JoinOverlappingTenons(self, l2):
            # What if a tenon is wholly inside another tenon?
            # Specially check circles? D curves?
            if len(l2) <= 1:
                return l2
            l = copy.copy(l2)
            i = 0
            newList = []
            while (len(l) > 0):
                poly1 = l[0]
                foundOverlap = False
                for poly2 in l[1:]:
                    if poly1.Overlap(poly2):            
                        # Join the tenons, remove each original tenon from list
                        # Add the new joined tenon to the list
                        joinedTenon = poly1.Add(poly2)
                        joinedTenon = joinedTenon[0]
                        foundOverlap = True
                        l.remove(poly2)
                        l.remove(poly1)
                        l = [joinedTenon] + l
                        break
                        
                if not foundOverlap:
                    # This tenon does not overlap with anything, remove it from original list
                    # and add to new list
                    newList.append(poly1)
                    l.remove(poly1)

            return newList
            
        #********************************************************************
        # Slow down the speed as we move into inner loops because we are removing 100%
        # of the material
        #********************************************************************
        def SlowDownGoingIn(self, path):
            origSpeed = self.currentSpeed
            halfSpeed = self.currentSpeed/2
            for i in range(0,len(path)):
                s = path[i]
                s = s[0:-1]
                # When going into an inner blob, slow down
                if s == "(Going In)":
                    if self.currentSpeed != halfSpeed:
                        s = self.IntSpeed(halfSpeed)[0] + " " + s
                    else:
                        s = ""
                # When coming out of an inner blob, speed up
                if s == "(Going Out)":
                    if self.currentSpeed != origSpeed:
                        s = self.IntSpeed(origSpeed)[0] + " " + s
                    else:
                        s = ""
                path[i] = s
            return path
        
        #********************************************************************
        # When most of a roughing pass is being done by a larger cutter,
        # We just need to get the outermost loops of the path. So remove
        # any paths deeper than 2.
        #********************************************************************
        def JustGetAFewLoops(self, path):
            depth = 0
            path2 = []
            for i in range(0,len(path)):
                s = path[i]
                if s == "(Going In)\n":
                    depth += 1
                if s == "(Going Out)\n":
                    depth -= 1
                if depth < 2:
                    path2 += [s]
            return path2
            
        #********************************************************************
        # Clear pixels in image
        #********************************************************************
#        def CheckAroundPixel(self, im, x,y):
#            if im[0][y][x] != 0:
#                l2 = [(x,y)]
#                im[0][y][x] = 0
#                return l2
#            return []
        #********************************************************************
        # I cannot use skimage.morphology.flood_fill (even with a tolerance)
        # because the values of the pixels in the blob are 1,2,3...(non-zero)
        # in skimage.morphology.flood_fill, the tolerance parameter is +/-
        # "im" is a numpy array
        #********************************************************************
        def ClearBlob(self, im, X, Y):
#            im2 = im[0]
#            skimage.morphology.flood_fill(im2, (Y, X), 0, connectivity=2, in_place=True)
#            return
            lr = [(X,Y)]
            ud = [(X,Y)]
            im2 = im[0]
            im2[Y][X] = 0
            count = 0
            while (len(lr) > 0) or (len(ud) > 0):
                ud2 = []
                lr2 = []
                ud3 = []
                lr3 = []
                for p in lr:
                    count += 1
                    x = p[0]
                    y = p[1]
                    xE = x+1
                    xW = x-1
                    yN = y+1
                    yS = y-1
                    while im2[y][xW] != 0:
                        ud2.append((xW,y))
                        im2[y][xW] = 0
                        xW -= 1
                    while im2[y][xE] != 0:
                        ud2.append((xE,y))
                        im2[y][xE] = 0
                        xE += 1

                    if im2[yN][xW] != 0:
                        ud2.append((xW,yN))
                        im2[yN][xW] = 0
                    if im2[yN][xE] != 0:
                        ud2.append((xE,yN))
                        im2[yN][xE] = 0
                    if im2[yS][xW] != 0:
                        ud2.append((xW,yS))
                        im2[yS][xW] = 0
                    if im2[yS][xE] != 0:
                        ud2.append((xE,yS))
                        im2[yS][xE] = 0

                for p in ud:
                    count += 1
                    x = p[0]
                    y = p[1]
                    xE = x+1
                    xW = x-1
                    yN = y+1
                    yS = y-1
                    while im2[yN][x] != 0:
                        lr2.append((x,yN))
                        im2[yN][x] = 0
                        yN += 1
                    while im2[yS][x] != 0:
                        lr2.append((x,yS))
                        im2[yS][x] = 0
                        yS -= 1

                    if im2[yN][xW] != 0:
                        lr2.append((xW,yN))
                        im2[yN][xW] = 0
                    if im2[yN][xE] != 0:
                        lr2.append((xE,yN))
                        im2[yN][xE] = 0
                    if im2[yS][xW] != 0:
                        lr2.append((xW,yS))
                        im2[yS][xW] = 0
                    if im2[yS][xE] != 0:
                        lr2.append((xE,yS))
                        im2[yS][xE] = 0
                lr = lr2
                ud = ud2
                
        #********************************************************************
        # Add an X,Y offset to every coordinate
        # No need to add to I,J coords as they are relative to the X,Y
        #********************************************************************
        def AddOffsetToPath(self, path, oX, oY):
            newPath = []
            floatingPointStr = "[-+]?(?:\d*\.\d+|\d+)"
            offArray = [oX, oY]
            charArray = "XY"
            for line in path:
                for i in range(0,2):
                    # Find X,Y coordinates
                    # {XY} {-+} {d.ddd or .ddd or d}
                    m = re.match( r'(.* )(' + charArray[i] + floatingPointStr + ')(.*)', line, re.M|re.I)
                    if m:
                        x = float(m.group(2)[1:]) + offArray[i]
                        line = m.group(1) + charArray[i] + "%0.4f" % x + m.group(3)
                newPath += [line]
            return newPath
        

        #********************************************************************
        # Cut a list of paths accurately (no trajectory blending) from z1 to z2
        #********************************************************************
        def CutAccuratePathList(self, l, z1, z2):
            fs = []
            for l2 in l:
                fs += self.CutAccuratePath(l2.points, z1, z2)
            return fs

        #********************************************************************
        # Cut a path accurately (no trajectory blending) from z1 to z2
        #********************************************************************
        def CutAccuratePath(self, l, z1, z2):
            path = self.IntPointsToPath(l,1)
            fs = self.IntDisableTrajectoryBlending()
            fs += self.CutPathFromZ1ToZ2(path, path, z1, z2)
            fs += self.RapidToZ(self.RapidHeight)
            fs += self.IntEnableTrajectoryBlending(0,0)
            return fs

        #********************************************************************
        # Cut a poly line from a list of points (vectors) starting 
        # at depth=z1 down to depth=z2
        #********************************************************************
        def CutShapeLine(self,listOfXYPoints,z1,z2):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            return self.IntCutShapeLine(listOfXYPoints,z1,z2)

        #********************************************************************
        # Perform a drill cycle at each point in the poly
        #********************************************************************
        def DrillCycle(self,listOfXYPoints,slowPeck,fastPeck,peckDepth,z2):
            self.CommentFunction(sys._getframe().f_code.co_name, str(locals()))
            return self.IntDrillCycle(listOfXYPoints,slowPeck,fastPeck,peckDepth,z2)

        #--------------------------------------------------------------------
        #--------------------------------------------------------------------
        # Move and Rapid Functions
        #--------------------------------------------------------------------
        #--------------------------------------------------------------------
        def RapidToXY(self,x,y):
            self.currentX = x
            self.currentY = y
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return ["G0 X%.4f Y%.4f" % (x * 1000, y * 1000)]
            else:
                return ["G0 X%.4f Y%.4f" % (x, y)]
       
        def RapidToZ(self,z):
            self.currentZ = z
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return ["G0 Z%.4f" % (z*1000)]
            else:
                return ["G0 Z%.4f" % (z)]
       
        def MoveToXY(self,x,y):
            self.currentX = x
            self.currentY = y
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return ["G1 X%.4f Y%.4f" % (x * 1000, y * 1000)]
            else:
                return ["G1 X%.4f Y%.4f" % (x, y)]
           
        def MoveToZ(self,z):
            self.currentZ = z
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return ["G1 Z%.4f" % (z * 1000)]
            else:
                return ["G1 Z%.4f" % (z)]
       
        def ArcToXY(self,x,y,xCenter,yCenter,G):
            self.currentX = x
            self.currentY = y
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return ["%s X%.4f Y%.4f I%.4f J%.4f" % (G, x * 1000, y * 1000, xCenter * 1000, yCenter * 1000)]
            else:
                return ["%s X%.4f Y%.4f I%.4f J%.4f" % (G, x, y, xCenter, yCenter)]
           
        def ArcToXY2(self,x,y,r,G):
            self.currentX = x
            self.currentY = y
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return ["%s X%.4f Y%.4f R%.5f" % (G, x * 1000, y * 1000, r * 1000)]
            else:
                return ["%s X%.4f Y%.4f R%.5f" % (G, x, y, r)]

        #--------------------------------------------------------------------
        #--------------------------------------------------------------------
        # Private Functions 
        #--------------------------------------------------------------------
        #--------------------------------------------------------------------

                
        #********************************************************************
        # Returns True if point is a clockwise curve
        #********************************************************************
        def IsClockwise(self, p):
            return p[4] == 1
                
        #********************************************************************
        # Internal - Cut a poly line from a list of points from z1 down to z2
        #********************************************************************
        def IntCutShapeLine(self,listOfXYPoints,z1,z2):
            fs = self.IntDisableTrajectoryBlending()
            newList = listOfXYPoints
            newList2 = self.ReverseListOfPoints(newList)
            path = self.IntPointsToPath(newList,0)
            path2 = self.IntPointsToPath(newList2,0)
            # If the path is closed (ends where we started) we can just do the same path
            if (newList[0][0] == newList[-1][0]) and (newList[0][1] == newList[-1][1]):
                fs += self.CutPathFromZ1ToZ2(path,path,z1,z2)
            else:
                fs += self.CutPathFromZ1ToZ2(path,path2,z1,z2)
            fs += self.RapidToZ(self.RapidHeight)
            fs += self.IntEnableTrajectoryBlending(0,0)
            return fs

        #********************************************************************
        # Internal - Drill Cycle
        # Once a CNC machine is in a mode like G81, G83, or G73 it just needs
        # to be sent to the next X,Y position and it will drill a hole
        # until it reaches the G80 command.
        # Note that X and Y coords are RELATIVE to the first hole!
        #********************************************************************
        def IntDrillCycle(self,listOfXYPoints,slowPeck,fastPeck,peckDepth,z2):
            newList = copy.copy(listOfXYPoints)
            p0 = newList[0]
            fs = ["G0 X%.4f Y%.4f" % (p0[0], p0[1])]
            if not slowPeck and not fastPeck:
                fs += ["G98 G81 R%.4f Z%.4f (G81 No Peck Drilling)" % (self.RapidHeight, -self.RapidHeight+z2)]
            elif slowPeck:
                # We peck down at 20% of the total depth
                fs += ["G98 G83 R%.4f Z%.4f Q%.4f (G83 Slow Peck Drilling - full retraction)" % (self.RapidHeight, -self.RapidHeight+z2, abs(peckDepth))]
            else:
                # We peck down at 20% of the total depth
                fs += ["G98 G73 R%.4f Z%.4f Q%.4f (G73 Fast Peck Drilling - partial retraction)" % (self.RapidHeight, -self.RapidHeight+z2, abs(peckDepth))]
            newList.pop(0)
            for p in newList:
                fs += ["X%.4f Y%.4f" % (p[0], p[1])]
            fs += ["G80"]
            return fs

        #********************************************************************
        # Reverse a list of points (needed to handle curved segments)
        #********************************************************************
        def ReverseListOfPoints(self, points):
            points2 = []
            for i in range(0,-len(points),-1):      
                p1 = points[i]
                p2 = points[i-1]
                if Blender4CNC.Polytoxogon.PointIsStraight(p1, p1):      
                    points2 +=  [(p2[0], p2[1])]
                else:
                    points2 +=  [(p2[0], p2[1], p1[2], p1[3], -p1[4])]
            return points2                
                
        #********************************************************************
        # Given a path of GCode, will cut this path at all z depths from z1 
        # to z2.
        # It will oscillate between the first path and second path
        #********************************************************************
        def CutPathFromZ1ToZ2(self,path,path2,z1,z2):
            # Rapid to the first point
            line = path[0]
            fs = ["G0" + line[2:] ]
            z = z1
            paths = [path, path2]
            ndx = 0 
            firstTime = True
            while (z > z2) or (firstTime and (z == z2)):
                firstTime = False
                # Cut the polys at this z depth
                z = max(z2, z + self.zStep)
                fs += self.MoveToZ(z) 
                fs += paths[ndx]
                ndx = (ndx + 1) % 2
            return fs
           
        #********************************************************************
        # Convert a list of points into a GCode path
        #********************************************************************
        def IntPointsToPath(self, points, plusOne):
            fs = []
            for ndx in range(0, len(points) + plusOne):
                i = ndx
                if ndx == len(points):
                    i = 0
                A = points[i]
                if Blender4CNC.Polytoxogon.PointIsStraight(A,A): 
                    fs += self.MoveToXY(A[0], A[1])
                else:
                    B = points[i-1]
                    xC = A[2] - B[0]
                    yC = A[3] - B[1]
                    
                    if self.IsClockwise(A):
                        GA = "G2"
                    else:
                        GA = "G3"
                    # Handle case where first point is a curve - we must first move to the 
                    # last point which is the start of the curve
                    # JUST PRETEND IT IS A LINE
                    if ndx == 0:
                        fs += self.MoveToXY(A[0], A[1])
                    else:
                        fs += self.ArcToXY(A[0], A[1], xC, yC, GA)
            return fs

        #********************************************************************
        # Adds initialization GCode commands at start of program
        #********************************************************************
        def InitProgramStringList(self, gcodePreAmble):
            s = []
            s += gcodePreAmble
            s.append("G0 Z%3.4f" % self.RapidHeight)
            return s

        #********************************************************************
        # Adds ending GCode commands at end of program
        #********************************************************************
        def EndProgramStringList(self):
            s = ["M5 M9 (Stop Spindle and Coolant)"]
            s.append("M30 (End Program)")
            return s

        #********************************************************************
        # Common tasks to start the finishing pass
        #********************************************************************
        def IntStartFinishing(self, finishingSpeedRatio):
            fs = [" ", "( Finishing Pass )"]
            self.oldSpeed = self.currentSpeed
            fs += self.IntSpeed(self.finishingSpeed)
            fs += self.IntDisableTrajectoryBlending()
            self.oldStepover = self.stepPercent
            self.stepPercent = 0.8
            return fs

        #********************************************************************
        # Common tasks to end the finishing pass
        #********************************************************************
        def IntEndFinishing(self):
            fs = self.IntEnableTrajectoryBlending(0,0)
            fs += self.IntSpeed(self.oldSpeed)
            self.stepPercent = self.oldStepover
            return fs
           
        #********************************************************************
        # Private internal function for cutting a circle
        #********************************************************************
        def IntCutCircle(self,x,y,radius,z1,z2):
            fs = self.RapidToXY(x-radius, y)
            z = z1
            while (z > z2):
                z = max(z2, z + self.zStep)
                fs += self.MoveToZ(z)
                fs += self.ArcToXY(x-radius,y,radius,0,"G2")
            fs += self.RapidToZ(self.RapidHeight)
            return fs

        #********************************************************************
        # Private internal function for cutting a circular pocket
        #********************************************************************
        def IntCutCircularPocket(self,xCenter,yCenter,radius,z1,z2):
            fs = []
        
            # Check arguments for errors
            if radius <= 0:
                raise Exception("ERROR radius must be greater than 0")
            if (self.cutterDiameter >= radius*2):
                raise Exception("ERROR current cutter diameter is too large for size of pocket")
            if z1 < z2:
                raise Exception("ERROR z1 must be greater than or equal to z2")
        
            # Get starting point
            rStep = (self.cutterDiameter / 2) * self.stepPercent
            xStep = rStep * 2
            stopX = (radius) - (self.cutterDiameter / 2) + xCenter
            stopRadius = stopX - xCenter
            z = z1
            while (z > z2):
                x = xCenter;
                y = yCenter;
                r = rStep;
                fs += self.RapidToXY(x,y)
                z = max(z2,z+self.zStep)
                fs += self.MoveToZ(z)
        
                # Cut the rest
                while (x < stopX):
                    x = min(stopX,x+xStep)
                    r = abs((x - self.currentX)/2)
                    fs += self.ArcToXY2(x,y,r,"G2")
                    r = abs(((xCenter-(x-xCenter)) - self.currentX)/2)
                    fs += self.ArcToXY2((xCenter-(x-xCenter)),y,r,"G2")
                    
                fs += self.ArcToXY2(xCenter+stopRadius,yCenter,stopRadius,"G2")
                fs += self.ArcToXY2(xCenter,y,stopRadius/2,"G2")
        
            # This is not used
            #if (self.numSpringCuts > 0):
            #    fs += self.ArcToXY2(stopX,yCenter,stopRadius/2,"G2")
            #    for i in range(0,self.numSpringCuts):
            #        fs += self.ArcToXY2(xCenter - radius + self.cutterDiameter/2,y,stopRadius,"G2")
            #        fs += self.ArcToXY2(xCenter + radius - self.cutterDiameter/2,y,stopRadius,"G2")
        
            fs += self.RapidToZ(self.RapidHeight)
            return fs

        #********************************************************************
        # Private internal function for finishing a circular pocket
        #********************************************************************
        def IntFinishCircularPocket(self,xCenter,yCenter,radius,z1,z2):
            fs = []
        
            # Check arguments for errors
            if radius <= 0:
                raise Exception("ERROR radius must be greater than 0")
            if self.cutterDiameter >= radius*2:
                raise Exception("ERROR current cutter diameter is too large for size of pocket")
            if z1 < z2:
                raise Exception("ERROR z1 must be greater than or equal to z2")
        
            # Get starting point
            rStep = (self.cutterDiameter / 2) * self.stepPercent
            xStep = rStep * 2
            stopX = (radius) - (self.cutterDiameter / 2) + xCenter
            stopRadius = stopX - xCenter
            z = z1
            while (z > z2):
                x = xCenter;
                y = yCenter;
                r = rStep;
                fs += self.RapidToXY(x,y)
                z = max(z2,z+self.zStep)
                fs += self.MoveToZ(z)
        
                fs += self.ArcToXY2(xCenter+stopRadius,yCenter,stopRadius/2,"G2")
                fs += self.ArcToXY2(xCenter-stopRadius,yCenter,stopRadius,"G2")
                fs += self.ArcToXY2(xCenter+stopRadius,yCenter,stopRadius,"G2")
                fs += self.ArcToXY2(xCenter,y,stopRadius/2,"G2")
        
            return fs

        #********************************************************************
        # Private internal function to set the current feed speed
        #********************************************************************
        def IntSpeed(self, spd):
            self.currentSpeed = spd
            return ["F%.4f" % spd]

        #********************************************************************
        # Private internal function to disable trajectory blending.
        #********************************************************************
        def IntDisableTrajectoryBlending(self):
            return ["G61 (Disable Trajectory Blending)"]

        #********************************************************************
        # Private internal function to enable trajectory blending.
        #********************************************************************
        def IntEnableTrajectoryBlending(self, P_tolerance, Q_tolerance):
            # G64 P0 is the same as G64
            return ["G64 (Enable Trajectory Blending)"]
            #return ["G64 P%.3f Q%.3f (Enable Trajectory Blending)" % (P_tolerance, Q_tolerance)]

        #********************************************************************
        # Write out the GCode program to a file
        #********************************************************************
        def WriteGCode(self, fname):
            with io.open(fname, "w") as f:
                f.write('\n'.join(self.ss))
        
        #********************************************************************
        # Add a comment in the GCode to record the function call
        #********************************************************************
        def CommentFunction(self, name, argsIn):
            self.ss.append(" ")
            # Remove any 'self' variable
            ndx1 = argsIn.find("'self':")
            if ndx1 != -1:
                ndx2 = argsIn.find(">, ")
                if ndx2 == -1:
                    ndx2 = argsIn.find(">}")
                    args = argsIn[0:ndx1] + argsIn[ndx2+1:]
                else:
                    args = argsIn[0:ndx1] + argsIn[ndx2+3:]
            else:
                args = argsIn
            # Check for embedded comments in args
            args = args.replace("(", "[")
            args = args.replace(")", "]")
            commentStr = name + " " + args
            # Check for length
            while len(commentStr) > 240:
                self.ss.append("( " + commentStr[0:240] + " )")
                commentStr = commentStr[240:]
            self.ss.append("( " + commentStr + " )")

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A Class to group 2d utility functions
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS Util2d
    class Util2d:
        
        def __init__(self):
            pass
        
        # Functions to handle math on 2D tuples
        def angle_signed(self, o): 
            x1 = self[0]
            y1 = self[1]
            x2 = o[0]
            y2 = o[1]
            a = atan2(x1*y2-y1*x2,x1*x2+y1*y2)
            return -a
        
        #**************************************************************************
        # Given an angle in radians - returns angle in range 0..2pi
        #**************************************************************************
        def MakeAngleBetween0and2pi(angle1):
            while angle1 >= (2*pi):
                angle1 = angle1 - (2 * pi)
            while angle1 < 0:
                angle1 = angle1 + (2 * pi)
            return angle1

        #**************************************************************************
        # Given two angles, returns the clockwise angle between them (from angle1
        # to angle2)
        #**************************************************************************
        def GetClockwiseAngleBetween(angle1, angle2):
            angle1 = Blender4CNC.Util2d.MakeAngleBetween0and2pi(angle1)
            angle2 = Blender4CNC.Util2d.MakeAngleBetween0and2pi(angle2)
            if angle1 >= angle2:
                ans = angle1 - angle2
            else:
                ans = (2 * pi) - (angle2 - angle1)
            return ans

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A Class to group 3d utility functions
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS Util3d
    class Util3d:
        
        def __init__(self):
            pass
        
        # Functions to handle math on 3D tuples
        def add3d(a,b):
            return (b[0]+a[0], b[1]+a[1], b[2]+a[2])
    
        def sub3d(self, a):
            return (self[0]-a[0], self[1]-a[1], self[2]-a[2])
        
        def dot3d(self, a):
            return self[0]*a[0] + self[1]*a[1] + self[2]*a[2]

        def lerp3d(self, a, t):
            """ Lerp. Linear interpolation from self to a"""
            x = self[0] + (a[0] - self[0])  * t
            y = self[1] + (a[1] - self[1])  * t
            z = self[2] + (a[2] - self[2])  * t
            return (x,y,z)
        
        def unit3d(self):
            """ Normalize. """
            mag = math.sqrt(self[0]**2 + self[1]**2 + self[2]**2)
            return (self[0]/mag, self[1]/mag, self[2]/mag)
            
        def cross3d(self, a):
            """ Cross. """
            return (self[1] * a[2] - self[2] * a[1], self[2] * a[0] - self[0] * a[2], self[0] * a[1] - self[1] * a[0])

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A Class to handle saving/loading gray PNG images
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS GrayImages
    class GrayImages:
        
        def __init__(self):
            pass
        
        #********************************************************************
        # Reads an image from a filename and returns it as a numpy array
        #
        # This is about 2.5% slower
        # Convert to tuple (for performance), then get every 4th value (red channel)
        #pixels2 = img.pixels[:]
        #pixels = [int(p*255) for p in pixels2[::4]]
        #pixels = bytearray(pixels)
        #a = numpy.frombuffer(pixels, dtype="uint8")
        #b = a.reshape(height, width)
        #d = numpy.flip(b,0)
        # Clean up and remove the temporary image
        #bpy.data.images.remove(img)
        #return d.astype(float)
        #********************************************************************
        def ReadGrayPNG(filename):
            # Remove image if it exists         
            if filename in bpy.data.images:
                # FAILS COVERAGE
                image = bpy.data.images[filename]
                bpy.data.images.remove(image)

            (name, ext) = os.path.splitext(filename)
            img = bpy.data.images.load(filename)
            (width, height) = img.size

            # Convert to tuple (for performance), create array, reshape
            b = numpy.array(img.pixels[:], dtype=numpy.float32).reshape((height, width, 4))
            b = b[:,:,0]    # get every 4th value (red channel)
            d2 = numpy.flip(b,0)
            d2 *= 255
            d2 = d2.astype(int)
            bpy.data.images.remove(img)
            return d2.astype(float)

        #*************************************************************************
        # Save numpy array image as PNG (grayscale)
        #*************************************************************************
        def SaveGrayPNG(filename,im):
            imA = numpy.flipud(im) / 255
            im2 = numpy.stack([imA,imA,imA,imA],2)
            im2[:,:,3] = 255 # Set alpha

            # Remove any temporary image that exists         
            name = "TEMP"
            if name in bpy.data.images:
                # FAILS COVERAGE
                image = bpy.data.images[name]
                bpy.data.images.remove(image)
            # Create an image called "TEMP"
            image = bpy.data.images.new(name, width=im.shape[1], height=im.shape[0])

            # assign pixels
            image.pixels = im2.ravel()

            # write image
            image.filepath_raw = filename
            image.file_format = 'PNG'
            image.save()    

            # Clean up and remove the temporary image
            bpy.data.images.remove(image)

    #***********************************************************************************************
    # The following code is a modified copy of pycsg from https://github.com/timknip/pycsg
    # (which in turn is a port of Evan Wallace's csg.js at https://github.com/evanw/csg.js/).
    # This includes all code between here and the marker END_CSG_END
    #
    # It was modified for the purpose of copying and pasting it into a larger python source file
    # so it could be easily added into Blender as part of an addon.
    # 
    # Modifications included:
    #   Prefixing "CSG" onto all the class names to avoid clashing with any classes of the same 
    #       name already defined in Blender or the addon.
    #
    # A bug was discovered with respect to creating a plane from a set of points and this 
    # precipitated the following modifications:
    #   Adding an equality operator to the Vector class.
    #   Adding a class method "fromNormalAndPoint" to the Plane class.
    #   Modifying the Plane.splitPolygon method to ignore any faces (polygons/planes) with zero area.
    #   Modifying the Polygon__init__ method to search for a valid plane normal from the point set.
    #
    # Changes were made to optimize performance
    #***********************************************************************************************

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A Class to perform CSG
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS CSG
    class CSG():
        """
        Constructive Solid Geometry (CSG) is a modeling technique that uses Boolean
        operations like union and intersection to combine 3D solids. This library
        implements CSG operations on meshes elegantly and concisely using BSP trees,
        and is meant to serve as an easily understandable implementation of the
        algorithm. All edge cases involving overlapping coplanar polygons in both
        solids are correctly handled.
        
        Example usage::
        
            from csg.core import CSG
            
            cube = CSG.cube();
            sphere = CSG.sphere({'radius': 1.3});
            polygons = cube.subtract(sphere).toPolygons();
        
        ## Implementation Details
        
        All CSG operations are implemented in terms of two functions, `clipTo()` and
        `invert()`, which remove parts of a BSP tree inside another BSP tree and swap
        solid and empty space, respectively. To find the union of `a` and `b`, we
        want to remove everything in `a` inside `b` and everything in `b` inside `a`,
        then combine polygons from `a` and `b` into one solid::
        
            a.clipTo(b);
            b.clipTo(a);
            a.build(b.allPolygons());
        
        The only tricky part is handling overlapping coplanar polygons in both trees.
        The code above keeps both copies, but we need to keep them in one tree and
        remove them in the other tree. To remove them from `b` we can clip the
        inverse of `b` against `a`. The code for union now looks like this::
        
            a.clipTo(b);
            b.clipTo(a);
            b.invert();
            b.clipTo(a);
            b.invert();
            a.build(b.allPolygons());
        
        Subtraction and intersection naturally follow from set operations. If
        union is `A | B`, subtraction is `A - B = ~(~A | B)` and intersection is
        `A & B = ~(~A | ~B)` where `~` is the complement operator.
        
        ## License
        
        Copyright (c) 2011 Evan Wallace (http://madebyevan.com/), under the MIT license.
        
        Python port Copyright (c) 2012 Tim Knip (http://www.floorplanner.com), under the MIT license.
        Additions by Alex Pletzer (Pennsylvania State University)
        """

        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        # A Class to represent a CSG polygon
        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        #COVERAGE_CLASS CSG.CSGPolygon
        class CSGPolygon():
            def __init__(self, vertices, plane):
                self.vertices = vertices
                self.plane = plane

            @classmethod
            def fromVertices(self_Class, vertices):
                return self_Class(vertices, Blender4CNC.CSG.GetPlaneForVertices(vertices))

            def __eq__(self, obj):
                if not isinstance(obj, Blender4CNC.CSG.CSGPolygon):
                    return False
                if self.vertices != obj.vertices:
                    return False
                if self.plane != obj.plane:
                    return False
                return True
            
            def __ne__(self, obj):
                return not self == obj

            def __repr__(self):
                return self.__str__()
            
            def __str__(self):
                return str(self.vertices) + " " + str(self.plane)
            
        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        # A Class to represent nodes in a CSG BSP tree
        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        #COVERAGE_CLASS CSG.CSGBSPNode
        class CSGBSPNode():
            """
            class CSGBSPNode

            Holds a node in a BSP tree. A BSP tree is built from a collection of polygons
            by picking a polygon to split along. That polygon (and all other coplanar
            polygons) are added directly to that node and the other polygons are added to
            the front and/or back subtrees. This is not a leafy BSP tree since there is
            no distinction between internal and leaf nodes.
            """
            def __init__(self, polygons=None):
                self.plane = None # CSGPlane instance
                self.front = None # BSPNode
                self.back = None  # BSPNode
                self.polygons = []
                if polygons:
                    self.build(polygons)

            def __eq__(self, obj):
                if not isinstance(obj, Blender4CNC.CSG.CSGBSPNode):
                    return False
                if not self.plane == obj.plane:
                    return False
                if not self.front == obj.front:
                    return False
                if not self.back == obj.back:
                    return False
                if not self.polygons == obj.polygons:
                    return False
                return True
    
            def __ne__(self, obj):
                return not self == obj

            def __repr__(self):
                return self.__str__()

            def __str__(self):
                return "\n" + self.__str2__(self, "")
                    
            def __str2__(self, node, indent):
                s = indent + "CSGBSPNode:\n"
                s += indent + "plane=" + str(node.plane) + "\n"
                if node.back != None:
                    s += indent + "back=\n" + self.__str2__(node.back, indent + "|   ")
                else:
                    s += indent + "back= None\n"
                if node.front != None:
                    s += indent + "front=\n" + self.__str2__(node.front, indent + "|   ")
                else:
                    s += indent + "front= None\n"
                if len(node.polygons) > 0:
                    s += indent + "polygons=\n"
                    for x in node.polygons:
                        s += indent + str(x) + "\n"
                else:
                    s += indent + "polygons= []\n"
                return s
                    
            def printPretty(self, indent = ""):
                indent +=  " " * 4
                print(indent, "polygons %d =" % len(self.polygons), self.polygons)       
                print(indent, "plane=", self.plane)       
                print(indent, "front=", self.front)       
                if self.front:
                    self.front.printPretty(indent)
                print(indent, "back=", self.back)       
                if self.back:
                    self.back.printPretty(indent)
                    
            # Convert solid space to empty space and empty space to solid space.
            def invert(self):
                for poly in self.polygons:
#                    Blender4CNC.CSG.flipPolygon(poly)
                    poly.vertices.reverse()
                    poly.plane = ((-poly.plane[0][0], -poly.plane[0][1], -poly.plane[0][2]), -poly.plane[1])
                self.plane = ((-self.plane[0][0], -self.plane[0][1], -self.plane[0][2]), -self.plane[1])
                if self.front: 
                    self.front.invert()
                if self.back: 
                    self.back.invert()
                temp = self.front
                self.front = self.back
                self.back = temp
                
            # Recursively remove all polygons in `polygons` that are inside this BSP tree.
            def clipPolygons(self, polygons):
                if not self.plane: 
                    return polygons[:]

                front = []
                back = []
                for poly in polygons:
                    Blender4CNC.CSG.splitPolygon(None, poly, front, back, front, back, self.plane[0], self.plane[1])

                if self.front: 
                    front = self.front.clipPolygons(front)

                if self.back: 
                    back = self.back.clipPolygons(back)
                else:
                    back = []

                front.extend(back)
                return front
                
            # Remove all polygons in this BSP tree that are inside the other BSP tree `bsp`.
            def clipTo(self, bsp):
                self.polygons = bsp.clipPolygons(self.polygons)
                if self.front: 
                    self.front.clipTo(bsp)
                if self.back: 
                    self.back.clipTo(bsp)
                
            # Return a list of all polygons in this BSP tree.
            def allPolygons(self):
                polygons = self.polygons[:]
                if self.front: 
                    polygons.extend(self.front.allPolygons())
                if self.back: 
                    polygons.extend(self.back.allPolygons())
                return polygons
                
            # Build a BSP tree out of `polygons`. When called on an existing tree, the
            # new polygons are filtered down to the bottom of the tree and become new
            # nodes there. Each set of polygons is partitioned using the first polygon
            # (no heuristic is used to pick a good split).
            def build(self, polygons):
                if len(polygons) == 0:
                    return
                if not self.plane: 
                    self.plane = (polygons[0].plane[0], polygons[0].plane[1])
                # add polygon to this node
                self.polygons.append(polygons[0])
                front = []
                back = []
                # split all other polygons using the first polygon's plane
                for poly in polygons[1:]:
                    # coplanar front and back polygons go into self.polygons
                    Blender4CNC.CSG.splitPolygon(None, poly, self.polygons, self.polygons, front, back, self.plane[0], self.plane[1])
                # recursively build the BSP tree
                if len(front) > 0:
                    if not self.front:
                        self.front = Blender4CNC.CSG.CSGBSPNode()
                    self.front.build(front)
                if len(back) > 0:
                    if not self.back:
                        self.back = Blender4CNC.CSG.CSGBSPNode()
                    self.back.build(back)

        #COVERAGE_CLASS CSG
        def __init__(self):
            self.polygons = []
        
        #********************************************************************
        def __eq__(self, obj):
            if not isinstance(obj, Blender4CNC.CSG):
                return False
            if self.polygons != obj.polygons:
                return False
            return True

        def __ne__(self, obj):
            return not self == obj

        def __repr__(self):
            return self.__str__()

        def __str__(self):
            s = "CSG Num polygons=" + str(len(csg.polygons)) + "\n"
            for i in range(0,len(csg.polygons)):
                poly1 = csg.polygons[i]
                s += str(i) + ": " + str(poly1.vertices) + "\n"
            return s


        @classmethod
        def fromPolygons(self_Class, polygons):
            csg = Blender4CNC.CSG()
            csg.polygons = polygons
            return csg
        
        def clone(self):
            csg = Blender4CNC.CSG()
            for p in self.polygons:
                csg.polygons.append(Blender4CNC.CSG.CSGPolygon(copy.copy(p.vertices), p.plane))            
            return csg
            
#        def toPolygons(self):
#            return self.polygons

#        def flipPolygon(poly):
#            poly.vertices.reverse()
#            poly.plane = ((-poly.plane[0][0], -poly.plane[0][1], -poly.plane[0][2]), -poly.plane[1])

        #Return list of vertices, polygons (cells), and the total
        #number of vertex indices in the polygon connectivity list
        #(count).
        def toVerticesAndPolygons(self):
            # Vertices that come in as 1.0 end up leaving as 1.0000000000000002
            # So I think eliminate this offset
            #offset = 1.234567890
            offset = 0.0
            verts = []
            polys = []
            vertexIndexMap = {}
            count = 0
            for poly in self.polygons:
                verts = poly.vertices
                cell = []
                for v in poly.vertices:
                    p = v
                    # use string key to remove degeneracy associated
                    # very close points. The format %.10e ensures that
                    # points differing in the 11 digits and higher are 
                    # treated as the same. For instance 1.2e-10 and 
                    # 1.3e-10 are essentially the same.
                    vKey = '%.10e,%.10e,%.10e' % (p[0] + offset, p[1] + offset, p[2] + offset)
                    if not vKey in vertexIndexMap:
                        vertexIndexMap[vKey] = len(vertexIndexMap)
                    index = vertexIndexMap[vKey]
                    cell.append(index)
                    count += 1
                polys.append(cell)
            # sort by index
            sortedVertexIndex = sorted(vertexIndexMap.items(), key=operator.itemgetter(1))
            verts = []
            for v, i in sortedVertexIndex:
                p = []
                for c in v.split(','):
                    p.append(float(c) - offset)
                verts.append(tuple(p))
            return verts, polys, count

        def GetPlaneForVertices(vertices):
            # DAVID ---------------------------------------------------------------------------
            # 8/18/2020 ---------------------------------------------------------------------------
            # If any of the 1st 3 points in a polygon happen to be exactly equal, this will
            # cause a divide by zero exception down the chain
            #self.plane = Blender4CNC.CSG.CSGPlane.fromPoints(vertices[0].pos, vertices[1].pos, vertices[2].pos)
            
            # To calculate the normal to a polygon in 3d space (and be robust), it is necessary
            # to calculate the cross product of all combinations of points as we go around
            # the polygon - the largest of these represents the normal of the largest inscribed triangle
            # and is the normal for the polygon
            # A robust solution is to find the largest cross product (P[i] - C) x (P[j] - C) 
            # for all i, j, (i < j) and normalize it. It will correspond to the largest inscribed triangle of the polygon.
            # By choosing C = (0,0,0), we can eliminate it from the calculations!
            # Actually, the above 3 lines can still fail!
            # Try this instead:        
            #    Choose any point C near the polygon (any vertex or mass center).
            #    Sum cross products (P[i] - C) x (P[i+1] - C) for all i (including last and first points pair).
            #    Normalize the sum vector.
            # Note that after step 2 you have a vector which has normal direction with proper orientation, and its 
            # magnitude is 2 S, where S is the area of your polygon. That's why it should work unless your polygon 
            # has zero or almost zero area.

            sum = (0,0,0)

            P0 = vertices[0]
            Pi = vertices[-1]
            vi = Blender4CNC.Util3d.sub3d(Pi,P0)
            for i in range(-1,len(vertices)-1):
                Pj = vertices[i+1]
                vj = Blender4CNC.Util3d.sub3d(Pj,P0)
                cross = Blender4CNC.Util3d.cross3d(vi,vj)
#                sum = Blender4CNC.add3d(sum, cross)
                sum = Blender4CNC.Util3d.add3d(sum, cross)
                vi = vj # Pass onto next loop
            
            # It is possible we were passed a set of points that have no area (in the polygon)
            lengthSqr = sum[0]**2 + sum[1]**2 + sum[2]**2
            if lengthSqr < 0.0000000001: # Zero
                return None
                
            n2 = Blender4CNC.Util3d.unit3d(sum)
            return (n2, Blender4CNC.Util3d.dot3d(n2,P0))
            
        def splitPolygon(self, polygon, coplanarFront, coplanarBack, front, back, normal, w):
            #        COPLANAR = 0 # all the vertices are within EPSILON distance from plane
            #        FRONT = 1 # all the vertices are in front of the plane
            #        BACK = 2 # all the vertices are at the back of the plane
            #        SPANNING = 3 # some vertices are in front, some in the back

            # Classify each point as well as the entire polygon into one of the above
            # four classes.
            numVertices = len(polygon.vertices)

            normX = normal[0]
            normY = normal[1]
            normZ = normal[2]

            polygonTypeFront = False
            polygonTypeBack = False

            vertexLocs = [0] * numVertices

            LOWER = w - Blender4CNC.REL_TOLERANCE # Tolerance to decide if on plane
            UPPER = w + Blender4CNC.REL_TOLERANCE
            for i,p in enumerate(polygon.vertices):
                t = normX*p[0] + normY*p[1] + normZ*p[2] # A dot product
                if t < LOWER: 
                    polygonTypeBack = True
                    vertexLocs[i] = 2 # BACK
                elif t > UPPER: 
                    polygonTypeFront = True
                    vertexLocs[i] = 1 # FRONT
            
            # Put the polygon in the correct list, splitting it when necessary.
            if polygonTypeFront and polygonTypeBack: # SPANNING
                f = []
                b = []
                for i in range(numVertices-1):
                    ti = vertexLocs[i]
                    vi = polygon.vertices[i]
                     
                    if ti == 0: # COPLANAR
                        f.append(vi)
                        b.append(vi)
                        needBoth = False
                    elif ti == 1: # FRONT
                        f.append(vi)
                        j = i+1
                        needBoth = (vertexLocs[j] == 2) # BACK
                    else: #if ti == BACK:
                        b.append(vi)
                        j = i+1
                        needBoth = (vertexLocs[j] == 1) # FRONT
                    if needBoth:
                        vj = polygon.vertices[j]
                        # interpolation weight at the intersection point
                        num = w - (normX*vi[0] + normY*vi[1] + normZ*vi[2]) # A dot product
                        vj_vi = (vj[0]-vi[0], vj[1]-vi[1], vj[2]-vi[2])
                        denom = (normX*vj_vi[0] + normY*vj_vi[1] + normZ*vj_vi[2]) # A dot product
                        t = num / denom
                        # intersection point on the plane
                        v = Blender4CNC.Util3d.lerp3d(vi, vj, t)
                        f.append(v)
                        b.append(v)

                # Catch the last vertex
                i = numVertices-1
                ti = vertexLocs[i]
                vi = polygon.vertices[i]
                needBoth = False
                 
                if ti == 0: # COPLANAR
                    f.append(vi)
                    b.append(vi)
                elif ti == 1: # FRONT
                    f.append(vi)
                    needBoth = (vertexLocs[0] == 2) # BACK
                else: #if ti == BACK:
                    b.append(vi)
                    needBoth = (vertexLocs[0] == 1) # FRONT
                if needBoth:
                    vj = polygon.vertices[0]
                    # interpolation weight at the intersection point
                    denom = Blender4CNC.Util3d.dot3d(normal, (Blender4CNC.Util3d.sub3d(vj,vi)))
                    t = (w - Blender4CNC.Util3d.dot3d(normal,vi)) / denom
                    # intersection point on the plane
                    v = Blender4CNC.Util3d.lerp3d(vi, vj, t)
                    f.append(v)
                    b.append(v)
                if len(f) >= 3: 
                    plane = Blender4CNC.CSG.GetPlaneForVertices(f)
                    if plane is not None:
                        polyT = Blender4CNC.CSG.CSGPolygon(f, plane)
                        front.append(polyT)
                if len(b) >= 3: 
                    plane = Blender4CNC.CSG.GetPlaneForVertices(b)
                    if plane is not None:
                        polyT = Blender4CNC.CSG.CSGPolygon(b, plane)
                        back.append(polyT)
            elif polygonTypeFront:
                front.append(polygon)
            elif polygonTypeBack:
                back.append(polygon)
            else: #if not (polygonTypeFront or polygonTypeBack): # COPLANAR
                p = polygon.plane[0]
                normalDotPlaneNormal = normX*p[0] + normY*p[1] + normZ*p[2] # A dot product
                if normalDotPlaneNormal > 0:
                    coplanarFront.append(polygon)
                else:
                    coplanarBack.append(polygon)

        #Return a new CSG solid representing space in either this solid or in the
        #solid `csg`. Neither this solid nor the solid `csg` are modified.::
        #    A.union(B)
        #    +-------+            +-------+
        #    |       |            |       |
        #    |   A   |            |       |
        #    |    +--+----+   =   |       +----+
        #    +----+--+    |       +----+       |
        #         |   B   |            |       |
        #         |       |            |       |
        #         +-------+            +-------+
        def union(self, csg):
            a = Blender4CNC.CSG.CSGBSPNode(self.clone().polygons)
            b = Blender4CNC.CSG.CSGBSPNode(csg.clone().polygons)
            a.clipTo(b)
            b.clipTo(a)
            b.invert()
            b.clipTo(a)
            b.invert()
            a.build(b.allPolygons());
            return Blender4CNC.CSG.fromPolygons(a.allPolygons())

        def printPretty(self):
            a = Blender4CNC.CSG.CSGBSPNode(self.clone().polygons)
            a.printPretty("")

        def __add__(self, csg):
            return self.union(csg)
            
        #Return a new CSG solid representing space in this solid but not in the
        #solid `csg`. Neither this solid nor the solid `csg` are modified.::

        #A.subtract(B)

        #+-------+            +-------+
        #|       |            |       |
        #|   A   |            |       |
        #|    +--+----+   =   |    +--+
        #+----+--+    |       +----+
        #     |   B   |
        #     |       |
        #     +-------+
        def subtract(self, csg):
            a = Blender4CNC.CSG.CSGBSPNode(self.clone().polygons)
            b = Blender4CNC.CSG.CSGBSPNode(csg.clone().polygons)
            a.invert()
            a.clipTo(b)
            b.clipTo(a)
            b.invert()
            b.clipTo(a)
            b.invert()
            a.build(b.allPolygons())
            a.invert()
            return Blender4CNC.CSG.fromPolygons(a.allPolygons())

        def __sub__(self, csg):
            return self.subtract(csg)
            
        #Return a new CSG solid representing space both this solid and in the
        #solid `csg`. Neither this solid nor the solid `csg` are modified.::
        #    A.intersect(B)
        #    +-------+
        #    |       |
        #    |   A   |
        #    |    +--+----+   =   +--+
        #    +----+--+    |       +--+
        #         |   B   |
        #         |       |
        #         +-------+
        def intersect(self, csg):
            a = Blender4CNC.CSG.CSGBSPNode(self.clone().polygons)
            b = Blender4CNC.CSG.CSGBSPNode(csg.clone().polygons)
            a.invert()
            b.clipTo(a)
            b.invert()
            a.clipTo(b)
            b.clipTo(a)
            a.build(b.allPolygons())
            a.invert()
            return Blender4CNC.CSG.fromPolygons(a.allPolygons())

        def __mul__(self, csg):
            return self.intersect(csg)
            
        # Return a new CSG solid with solid and empty space switched. This solid is
        # not modified.
        def inverse(self):
            csg = self.clone()
            #map(lambda p: p.flip(), csg.polygons)
#            for i in range(0,len(csg.polygons)):
#                Blender4CNC.CSG.flipPolygon(csg.polygons[i])
            for poly in csg.polygons:
                poly.vertices.reverse()
                poly.plane = ((-poly.plane[0][0], -poly.plane[0][1], -poly.plane[0][2]), -poly.plane[1])
            return csg

    #***********************************************************************************************
    #***********************************************************************************************
    #***********************************************************************************************
    # END_CSG_END
    #***********************************************************************************************
    #***********************************************************************************************
    #***********************************************************************************************



    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # 
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS Im2GCodeSettings
    class Im2GCodeSettings():
        
        def __init__(self):
            carving_width = 1.0
            carving_height = 1.0
            rough_dia = 1.0
            final_dia = 1.0
            carve_dia = 1.0
            ystep = 1.0
            zstep = 1.0
            max_depth = 1.0
            rapid_height = 1.0
            cutting_speed = 1.0
            acceleration = 1.0
            rapid_speed = 1.0
            number_layers = 1
            laminate_thickness = 1.0
            layers_grid = [[0,1]]
            clean_up = "yes"
            imagemagick_path = ""
            file_name = ""
            
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Exception class raised by Polytoxogon
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS PolyException
    class PolyException(Exception): 
        def __init__(self,*args,**kwargs):
            Exception.__init__(self,*args,**kwargs)
            
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A Class to handle processing an image (No longer used from the UI panel, only from other code)
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS Im2GCode
    class Im2GCode() :
#        bl_idname = "mesh.process_image"
#        bl_label = "Process Image"
#        bl_options = {"REGISTER", "UNDO"}

        #********************************************************************
        # 
        #********************************************************************
        def DEBUG_METHOD_HEADER(self, tf = False):
            methodName = self.__class__.__name__ + "." + inspect.stack()[1][3]
            indent = None
            self.debug[methodName] = tf
            if self.debug[methodName]:
                indent = " " * len(inspect.stack()) * 2
                print(indent, methodName, "*" * 30)
            return (methodName, indent, self.debug[methodName])
        
        def __init__(self):
            self.debug = {}
            pass

        #*************************************************************************
        # This function gets called when the user clicks the "Process Image" 
        # button.
        #*************************************************************************
        def Go_Image2GCode(self, i2g) :
            # Get the GUI parameters
            self.i2g = i2g
            
            self.Mgk = ImageMagick()

            startTime = datetime.datetime.now()
            self.layername = ""
            self.GetCalculatedParams()
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                print("Rough passes at depths: ", [round(x,4) for x in self.layer0Depths])
            else:
                print("Rough passes at depths: ", [round(x,2) for x in self.layer0Depths])
            if len(self.layerNDepths) > 0:
                # FAILS COVERAGE
                if (bpy.context.scene.unit_settings.system == "METRIC"):
                    print("Rough passes at depths (other layers): ", [round(x,4) for x in self.layerNDepths])
                else:
                    print("Rough passes at depths (other layers): ", [round(x,2) for x in self.layerNDepths])
            
            print("Image size = %d x %d" % (self.cols, self.rows))
            print("Scaling Image")

            #********************************
            # Scale image to final resolution
            #********************************
            # The image dimensions may not be a integer multiple of the step
            # and the image aspect ratio may not be the same aspect ratio as the desired result
            # therefore we actually need a ystep and a xstep
            # i.e. if want 6" and stepping every inch that means we have 7 cols (so must add 1)
            print("self.i2g.ystep=", self.i2g.ystep)
            newXYPerInch = 1 / self.i2g.ystep
            print("newXYPerInch =", newXYPerInch)
            newX = newXYPerInch * self.i2g.carving_width + 1
            newY = newXYPerInch * self.i2g.carving_height + 1
            print("self.i2g.carving_width =", self.i2g.carving_width)
            print("self.i2g.carving_height =", self.i2g.carving_height)
#            imageScale = ((self.i2g.carving_width / self.i2g.ystep)+1) / float(self.cols)

            # This is the desired step size
            origYStep = self.i2g.ystep
            print("original ystep =", self.i2g.ystep)
            origXYPerInch = 1 / self.i2g.ystep
            
            print("self.i2g.carving_height=", self.i2g.carving_height)
            print("origXYPerInch=", origXYPerInch)
            numRows = self.i2g.carving_height * origXYPerInch
            print("numRows=", numRows)
            numRows = round(numRows)
            newXYPerInch = numRows / self.i2g.carving_height
            print("newXYPerInch=", newXYPerInch)
            self.i2g.ystep = 1 / newXYPerInch
            print("actual ystep =", self.i2g.ystep)
            numRows += 1
            
#            numCols = self.i2g.carving_width * origXYPerInch
#            numCols = round(numCols)
#            newXYPerInch = numCols / self.i2g.carving_width
#            self.i2g.xstep = 1 / newXYPerInch
#            print("actual xstep =", self.i2g.xstep)
#            numCols += 1

            # "ystep" is the resolution of the image - it is important to keep this the same for
            # the x and y in order to keep the "pixels" square when it comes to using the larger 
            # bits for roughing passes, however, we scale the X and Y axes differently (as
            # necessary) to match the desired output aspect ratio            
            imageScale = ((self.i2g.carving_height / self.i2g.ystep)+1) / float(self.rows)
            imageScaleX = ((self.i2g.carving_width / self.i2g.ystep)+1) / float(self.cols)
            self.filename = os.path.splitext(self.i2g.file_name)[0]
            
            imA = Blender4CNC.GrayImages.ReadGrayPNG(self.i2g.file_name)
            x = imA.shape[1]
            y = imA.shape[0]
            print("Image cols,rows=", x,y)
            print("imageScale, imageScaleX=", imageScale, imageScaleX)
            x = round(x * imageScaleX)
            y = round(y * imageScale)
            print("Scaled image cols,rows=", x, y)
            print("Actual width, height=", (x-1) * self.i2g.ystep, (y-1) * self.i2g.ystep)
#            x = newX
#            y = newY
#            print("Scaled x,y=", x,y)
            
            # In the event that the aspect ratio of the image does not match the desired output
            # aspect ratio and that the dimensions are not exactly divisible by the step, we end up
            # with an image where the height in pixels will end up perfectly on the dimensions, but
            # the width in pixels will have a small amount of error (relative to the size of the step).
            # Therefore, when generating GCode, each pizel beginning from column 0 is placed at a position
            # of the step size multiplied by an integer but the pixel in the last column is placed at the
            # absolute position of the image width. The step between the last and next-to-last pixel
            # may be less than or more than the step size (but never more than twice the step size). 
            # In this way, the width of the carving will always end up exactly as specified.
            # For a very large bit or step size (e.g. 1"), the error on the right-hand edge *may* be 
            # noticeable to the human eye for certain combinations but why would anyone use such a large 
            # bit/step for these types of images?
            # The best/safest option is to choose a step size that divides evenly into the image height
            # and width (e.g. for 17.6" high by 12.1" wide, choose 0.1" (prototyping) or 0.01" (finished).
            imA01Scaled = skimage.transform.resize(imA, (y, x))
#            imA01Scaled = skimage.transform.resize(imA, (numRows, numCols))
            
            self.ext = ".png"

            #********************************
            # After scaling - the parameters change!
            #********************************
            self.cols = imA01Scaled.shape[1]
            self.rows = imA01Scaled.shape[0]
            print("New Image size = %d x %d" % (self.cols, self.rows))
            print("Size (in bytes) of new image:", imA01Scaled.nbytes)
            print("Size (in bytes) of working canvas per image stage:", imA01Scaled.nbytes * len(self.layer0Depths))
            # Linux will kill the Blender process if the memory usage is too extreme!
            if imA01Scaled.nbytes * len(self.layer0Depths) > 100000000: # 100M
                str2 = "ERROR - Resolution of depth image with YStep produces a resolution\nwhich is too large (working canvas exceeds 100Mb)."
                raise Exception(str2)
            

            #********************************
            # Draw box around image
            #********************************
            imA01Scaled[0,:] = 255
            imA01Scaled[:,0] = 255
            imA01Scaled[self.rows-1,:] = 255
            imA01Scaled[:,self.cols-1] = 255
            imA01Scaled = imA01Scaled / 255

            # Calculate the size of a pixel in inches
            self.pixelInInches = self.i2g.carving_width / (self.cols-1)

            # Calculate the exact radius of the final cutter in "pixel" units
            radius = (self.i2g.final_dia / 2) / self.pixelInInches

            # Layers need to be clipped and scaled (if not doing laminations this does not hurt)
            for i in range(0, self.i2g.number_layers):
                # If doing laminations, each layer of image needs to be clipped and scaled
                black = float(self.layers[i]["MinPixel"]) / self.MAX_PIXEL_VALUE
                white = float(self.layers[i]["MaxPixel"]) / self.MAX_PIXEL_VALUE
                mult = 1.0/(white-black);
                imA10SmoothStretch = (imA01Scaled - black) * mult

                # Load in the image
                im = imA10SmoothStretch * 255

                #****************************************************************
                # Steep gradients in the image cannot be realized due to the 
                # cutter geometry - must specially "smooth" the image
                #****************************************************************
                k = -(self.GetKernel(radius))
                im2 = scipy.ndimage.grey_dilation(im, size=(radius*2+1,radius*2+1), structure=k)
                print("Go_Image2GCode saving file: ", self.filename + "-L" + str(i) + "-A10-SMOOTH" + self.ext)
                Blender4CNC.GrayImages.SaveGrayPNG(self.filename + "-L" + str(i) + "-A10-SMOOTH" + self.ext, im2)
            # End for i

            # The starting position of the cutter
            self.lastX = 0
            self.lastY = 0
            self.lastZ = 0

            # Call "Go_Image2GCode_Layer" function for all layers to process and write all gcode
            self.outFileNames = []
            self.listOfDepths = self.layer0Depths
            oldMaxDepth = self.i2g.max_depth
            try:
                for i in range(0, self.i2g.number_layers):
                    self.layername = "-L" + str(i)
                    self.i2g.max_depth = self.layers[i]["MaxDepth"]
                    self.Go_Image2GCode_Layer()
                    self.listOfDepths = self.layerNDepths
            except: 
                # FAILS COVERAGE               
                self.i2g.max_depth = oldMaxDepth
                raise
            self.layername = ""

            # Also add GCode files to combine layers of gcode into one gcode file
            if self.i2g.number_layers > 1:
                # FAILS COVERAGE               
                self.CombineGCodeLayers(self.filename)

            # Delete temporary image files if required
#            if (i2g.clean_up == "yes"):
            if True:
                print("Cleaning up temporary files")
                try:
                    for suffix in ["-L*-A*.png", "-*.txt", "-*.pgm", "-B20-ROW*.png", "-L*-B*.png", "-A01-SCALED.png"]:
                        for f in glob.glob(self.filename + suffix):
                            os.remove(f)
                except:
                    # FAILS COVERAGE               
                    print("Unexpected error while cleaning up:", sys.exc_info()[0])
                    pass

            # Print how long the process took
            endTime = datetime.datetime.now()
            d = endTime - startTime
            print("Elapsed time: ", d)
                
            #print("Im2GCode returning")        
            return self.outFileNames

    #        # Get image info 
    #        (WIDTH, HEIGHT) = self.GetImageDimensions(self.filename + "-L0-B16-LARGECUTX.png")
    #        ASPECT = WIDTH / HEIGHT
    #        WIDTH = i2g.carving_width
    #        HEIGHT = WIDTH/ASPECT

    #        # Read in the 4 GCode files and create curves for each
    #        py2gcodeView = bpy.Py2GCodeView()

    #        materialSize = ((0, WIDTH), (0, HEIGHT), (-1,0))
    #        materialResolution = 0.05

    #        locs = ((-WIDTH,0,0), (0,0,0), (-WIDTH,-HEIGHT,0), (0,-HEIGHT,0))
    #        cutters = (self.i2g.rough_dia, self.i2g.final_dia, self.i2g.final_dia, self.i2g.final_dia)
    #        mats = ("Cyan", "Magenta", "Yellow", "Blue")
    #        pathMats = ("Red", "Green", "Blue", "Cyan")
    #        images = (self.filename + "-L%d-B16-LARGECUTX.png" , self.filename + "-L%d-B19-SMALLCUTX.png", self.filename + "-L%d-B14-FINALCUTX.png", "")
    #        fname = self.filename + "-L%d-%d.ngc"
    #        for level in range(0,i2g.number_layers):
    #            for phase in range(0,4):
    #                imageName = images[phase]
    #                if (images[phase] != ""):
    #                    imageName = images[phase] % level
    #                py2gcodeView.VisualizeGCode(fname % (level, phase+1), materialSize, materialResolution, cutters[phase],
    #                        "L%d-%d" % (level, phase+1), mats[phase], (locs[phase][0],locs[phase][1],2*level), (0,0,0), 
    #                        materialSize[2][0], imageName, (images[phase] == ""), pathMats[phase])
    #                        

    #        # If multiple layers        
    #        if self.i2g.number_layers > 1:
    #            grid = literal_eval(self.i2g.layers_grid)
    #            gridRows = len(grid)
    #            gridCols = len(grid[0])

    #            images = (self.filename + "-B31-GRIDCUTX.png" , self.filename + "-B32-GRIDCUTX.png", self.filename + "-B33-GRIDCUTX.png", "")
    #            materialSize = ((0, gridCols*WIDTH), (0, gridRows*HEIGHT), (-1,0))
    #            locs = ((-gridCols*WIDTH,0,0), (0,0,0), (-gridCols*WIDTH,-gridRows*HEIGHT,0), (0,-gridRows*HEIGHT,0))
    #            for phase in range(0,4):
    #                py2gcodeView.VisualizeGCode(self.filename + "-Grid-%d.ngc" % (phase+1), materialSize, materialResolution, cutters[phase],
    #                    "Grid-%d" % (phase+1), mats[phase], (locs[phase][0]+2*WIDTH+gridCols*WIDTH,locs[phase][1],0), (0,0,0), 
    #                    materialSize[2][0], images[phase], (images[phase] == ""), pathMats[phase])

        #****************************************************************
        # This function does most of the work of turning an image into
        # gcode
        #****************************************************************
        def Go_Image2GCode_Layer(self):
            imName = self.filename + self.layername
            # We want to stay a margin of error above the smoothed image heights
            bumpHeight = ((- self.finalBitRadius / 2) / self.i2g.max_depth)
            imA = Blender4CNC.GrayImages.ReadGrayPNG(imName + "-A10-SMOOTH.png")
            imA10Smooth = copy.copy(imA)
            imA /= 255
            imA += bumpHeight
            imA = numpy.where(imA>1, 1, imA)
            x = imA.shape[0] + 2
            y = imA.shape[1] + 2
            # Put a white border around image
            imB = numpy.ones((x,y))
            imB *= 255
            imB[1:x-1, 1:y-1] = imA
            imA = imB
            # Now threshold it at multiple levels and vertically stack
            images = []
            for i in range(0,len(self.listOfDepths)):
                d = self.listOfDepths[i]
                thresh = 100-100*(d/self.i2g.max_depth)
                thresh /= 100
                im = numpy.where(imA>thresh, 0, 255)
                images.append(im)
            imB = numpy.vstack(tuple(images))

            # Do not check base layer for orphaned material
            if (self.layername != "-L0"):
                # FAILS COVERAGE
                print("Bridging orphaned material.")
                inputFile = imName + "-A11-LAYERS.png"
                finalBridgesFile = imName + "-A10-SMOOTH.png"
                self.HandleMultiLayerOrphans(inputFile, finalBridgesFile)
                
            imA =imB.astype(float)
            imA11 = copy.copy(imA)
            imA11Eroded = copy.copy(imA)
            imA12 = copy.copy(imA)
            imA13 = copy.copy(imA)
            imA14 = copy.copy(imA)
            imA14FinalCut = copy.copy(imA)
            imA15 = copy.copy(imA)
            imA16 = copy.copy(imA)
            imA17 = copy.copy(imA)
            imA18 = copy.copy(imA)
            imA19 = copy.copy(imA)

            imA11 /= 255

            # Erode image
            k = self.GetDiscKernel(self.finalBitPixelRadius+0.3)
            #print("Eroding image (A11->A12)...")
            scipy.ndimage.morphology.binary_erosion(imA11, structure=k, output=imA12)
     
            # Dilate image
            #print("Dilate image (A12->A13)...")
            self.DILATE(imA12, imA13, self.finalBitPixelRadius-1+0.3)

            # Subtract image A13 from A11
            imA14 = imA11 - imA13
            imA14 = numpy.where(imA14<0, 0, imA14)

            # Erode image
            k = self.GetDiscKernel(self.roughBitPixelRadius-self.finalBitPixelRadius+0.3)
            #print("Eroding image (A12->A15)...")
            scipy.ndimage.morphology.binary_erosion(imA12, structure=k, output=imA15)

            # Dilate image
            print("Dilate image (A15->A16)...")
            self.DILATE(imA15, imA16, self.roughBitPixelRadius+0.3)

            # Dilate image
            print("Dilate image (A15->A17)...")
            self.DILATE(imA15, imA17, self.roughBitPixelRadius-self.finalBitPixelRadius+0.3)

            # Subtract image A17 from A12
            imA18 = imA12 - imA17
            imA18 = numpy.where(imA18<0, 0, imA18)

            # Dilate image
            #print("Dilate image (A15->A19)...")
            self.DILATE(imA15, imA19, self.finalBitPixelRadius+0.3)
            
            # "Binify" layers and flatten
            imB16 = self.BinifyAndFlatten(imA16)

            # "Binify" layers and flatten
            imB19 = self.BinifyAndFlatten(imA19)
            # "Darken" the composite of B19 and B16 (choose the darkest pixels between the two images
            imB19 = numpy.minimum(imB16, imB19)
            
            # Dilate image
            #print("Dilate image (A14->A14FinalCut)...")
            self.DILATE(imA14, imA14FinalCut, self.finalBitPixelRadius+0.3)
            
            # "Binify" layers and flatten
            imB14 = self.BinifyAndFlatten(imA14FinalCut)
            # "Darken" the composite of B19 and B14 (choose the darkest pixels between the two images)
            imB14 = numpy.minimum(imB14, imB19)
            
            imA10Smooth /= 255
            imA10SmoothBorder = self.AddWhiteBorder(imA10Smooth)

            # Erode image with square kernel (3x3 all ones)
            k = numpy.ones((3,3))
            #print("Eroding image (A11->A11Eroded)...")
            scipy.ndimage.morphology.binary_erosion(imA11, structure=k, output=imA11Eroded)
            # Subtract image imA11Eroded from A11
            imA14Final = imA11 - imA11Eroded
            imA14Final = numpy.where(imA14Final<0, 0, imA14Final)

            # Save images
            if Blender4CNC.DEBUG_DEPTH_IMAGES:
                # FAILS COVERAGE
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A11.png", imA11 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A12-SMALL.png", imA12 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A13-SMALLCUT.png", imA13 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A14.png", imA14 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A15-LARGE.png", imA15 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A16-LARGECUT.png", imA16 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A17-LARGECUTSMALL.png", imA17 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A18-SMALL.png", imA18 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A19-SMALLCUT.png", imA19 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-B16-LARGECUTX.png", imB16 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-B19-SMALLCUTX.png", imB19 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A14-FINALCUT.png", imA14FinalCut * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-B14-FINALCUTX.png", imB14 * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A10-SMOOTHBORDER.png", imA10SmoothBorder * 255)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A14-FINAL.png", imA14Final * 255)

            #****************************************************************
            # Check for ring structures
            #****************************************************************
            imA15 = self.HandleRingStructures(imA15)
            imA18 = self.HandleRingStructures(imA18)
            if Blender4CNC.DEBUG_DEPTH_IMAGES:
                # FAILS COVERAGE
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A15-LARGE-POSTRING.png", imA15 * 255)

            #****************************************************************
            # Images for showing cut material
            #****************************************************************
            imA22FinalDist = self.DISTANCE(imA14Final * 255)
            imA20LargeDist = self.DISTANCE(imA15 * 255)
            imA21SmallDist = self.DISTANCE(imA18 * 255)
            if Blender4CNC.DEBUG_DEPTH_IMAGES:
                # FAILS COVERAGE
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A22-FINALDIST.png", imA22FinalDist)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A20-LARGEDIST.png", imA20LargeDist)
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-A21-FINALDIST.png", imA21SmallDist)
                X

            #****************************************************************
            # Process the distance images for the roughing passes 
            #****************************************************************
            self.innerPathToleranceEnableCount = 0 # Start in G64 mode
            fname = self.filename + self.layername + "%s" + self.ext
            print("Processing GCode for Large Rough Cutter.")
            largeRoughGCode = self.GetGCodeForDistanceImage(fname % "-A20-LARGEDIST", fname % "-A15-LARGE", self.roughBitPixelRadius, len(self.listOfDepths), True, imA20LargeDist, imA15 * 255)
            print("Processing GCode for Small Rough Cutter.")
            smallRoughGCode = self.GetGCodeForDistanceImage(fname % "-A21-SMALLDIST", fname % "-A18-SMALL", self.finalBitPixelRadius, 0, False, imA21SmallDist, imA18 * 255)
            print("Processing GCode for Small Final Cutter.")
            finalRoughGCode = self.GetGCodeForDistanceImage(fname % "-A22-FINALDIST", fname % "-A14-FINAL", self.finalBitPixelRadius, 0, False, imA22FinalDist, imA14Final * 255)
            finalRoughGCode = ["G61 (Disable Trajectory Blending)\n"] + finalRoughGCode

            #****************************************************************
            # Load in the image
            #****************************************************************
            im = imA10Smooth * 255

            # We flip the image because 0,0 is at top left, whereas in G-Code,
            # 0,0 is at bottom left
            im = numpy.flipud(im)
            
            #***************************************************************
            # Go through the smooth image one row at a time.
            # For each row, get the Z profile as a path, simplify it and
            # create the G-Code for it
            #****************************************************************
            finalGCode = []
            path = []
            # Because this is the first point, and given how GetGCodeForPointLiteralZ works,
            # we upset the last value of Y deliberately
            self.lastY = -1
            finalGCode.append(self.GetGCodeForPointLiteralZ(0, 0, self.i2g.rapid_height))
            print("Processing GCode for final pass.")
            #print("self.rows, self.cols=", self.rows, self.cols)
            for r in range(0,self.rows):
                path = []

                path.append("(Row " + str(r) + ", " + str(self.pixelInInches*r) + ")\n")
                
                # Zig-zag across image by rows
                if ((r % 2) == 1):
                    path.append(self.GetGCodeForPointActualZ_LastCol(self.cols-1, r, im[r,self.cols-1]))
                    c = self.cols-2
                    while (c >= 1):
                        # Add any point at which we detect a change in gradient
                        if ((im[r,c] - im[r,c+1]) != (im[r,c-1] - im[r,c])):
                            path.append(self.GetGCodeForPointActualZ(c, r, im[r,c]))
                        c -= 1
                    # Add in the last point
                    path.append(self.GetGCodeForPointActualZ(0, r, im[r,0]))
                else:
                    path.append(self.GetGCodeForPointActualZ(0, r, im[r,0]));
                    for c in range(1, (self.cols-1)):
                        # Add any point at which we detect a change in gradient
                        if ((im[r,c] - im[r,c-1]) != (im[r,c+1] - im[r,c])):
                            path.append(self.GetGCodeForPointActualZ(c, r, im[r,c]))
                    # Add in the last point
                    path.append(self.GetGCodeForPointActualZ_LastCol(self.cols-1, r, im[r,self.cols-1]))

                finalGCode += path
            # End for r    
            finalGCode.append(self.GetGCodeForSafeZ());

            fname = self.i2g.outBaseName
            self.WriteGCode(largeRoughGCode, fname + self.layername + "-1.ngc", self.i2g.rough_dia, "rough");
            self.WriteGCode(smallRoughGCode, fname + self.layername + "-2.ngc", self.i2g.final_dia, "rough");
            self.WriteGCode(finalRoughGCode, fname + self.layername + "-3.ngc", self.i2g.final_dia, "final");
            self.WriteGCode(finalGCode, fname + self.layername + "-4.ngc", -1, "");
            self.outFileNames.append(fname + self.layername + "-1.ngc")
            self.outFileNames.append(fname + self.layername + "-2.ngc")
            self.outFileNames.append(fname + self.layername + "-3.ngc")
            self.outFileNames.append(fname + self.layername + "-4.ngc")
        # End Go_Image2GCode_Layer        
        def Go_Image2GCode_Layer(self):
            imName = self.filename + self.layername

            # We want to stay a margin of error above the smoothed image heights
            bumpHeight = ((- self.finalBitRadius / 2) / self.i2g.max_depth)
            imA = Blender4CNC.GrayImages.ReadGrayPNG(imName + "-A10-SMOOTH.png")
            imA10Smooth = copy.copy(imA)
            imA /= 255
            imA += bumpHeight
            imA = numpy.where(imA>1, 1, imA)
            x = imA.shape[0] + 2
            y = imA.shape[1] + 2
            # Put a white border around image
            imB = numpy.ones((x,y))
            imB *= 255
            imB[1:x-1, 1:y-1] = imA
            imA = imB
            # Now threshold it at multiple levels and vertically stack
            images = []
            for i in range(0,len(self.listOfDepths)):
                d = self.listOfDepths[i]
                thresh = 100-100*(d/self.i2g.max_depth)
                thresh /= 100
                im = numpy.where(imA>thresh, 0, 255)
                images.append(im)
            imB = numpy.vstack(tuple(images))

            # Do not check base layer for orphaned material
            if (self.layername != "-L0"):
                # FAILS COVERAGE
                print("Bridging orphaned material.")
                inputFile = imName + "-A11-LAYERS.png"
                finalBridgesFile = imName + "-A10-SMOOTH.png"
                self.HandleMultiLayerOrphans(inputFile, finalBridgesFile)
                
            imA =imB.astype(float)
            imA11 = copy.copy(imA)
            imA11 /= 255
    
            # NEW SECTION *******************************************
            #print("Go_Image2GCode_Layer C imagesize in bytes", imA11.nbytes)
            imageCount = 0
            imLayers = imA11
            imLargeFlatCenter = copy.copy(imA11)
            imLargeFlatCut = copy.copy(imA11)
            imLargeFlatDist = copy.copy(imA11)
            imLayersAfterLargeFlat = copy.copy(imA11)
            imSmallFlatCenter = copy.copy(imA11)
            imSmallFlatCut = copy.copy(imA11)
            imSmallFlatDist = copy.copy(imA11)
            imLayersAfterSmallFlat = copy.copy(imA11)
            imSmallBallDist = copy.copy(imA11)

            # Erode image by the large flat cutter
            k = self.GetDiscKernel(self.roughBitPixelRadius+0.3)
            scipy.ndimage.morphology.binary_erosion(imLayers, structure=k, output=imLargeFlatCenter)
            #****************************************************************
            # Check for ring structures
            #****************************************************************
            imLargeFlatCenter = self.HandleRingStructures(imLargeFlatCenter)
            # Distance image for the large flat cutter
            imLargeFlatDist = self.DISTANCE(imLargeFlatCenter * 255)
            # Dilate to see what pixels got removed by the large flat cutter
            self.DILATE(imLargeFlatCenter, imLargeFlatCut, self.roughBitPixelRadius-1+0.3)
            # See what pixels are left to be removed
            imLayersAfterLargeFlat = imLayers - imLargeFlatCut
            # Erode image by the small flat cutter
            k = self.GetDiscKernel(self.finalBitPixelRadius+0.3)
            scipy.ndimage.morphology.binary_erosion(imLayersAfterLargeFlat, structure=k, output=imSmallFlatCenter)
            #****************************************************************
            # Check for ring structures
            #****************************************************************
            imSmallFlatCenter = self.HandleRingStructures(imSmallFlatCenter)
            # Distance image for the small flat cutter
            imSmallFlatDist = self.DISTANCE(imSmallFlatCenter * 255)
            # Dilate to see what pixels got removed by the small flat cutter
            self.DILATE(imSmallFlatCenter, imSmallFlatCut, self.finalBitPixelRadius-1+0.3)
            # See what pixels are left to be removed
            imLayersAfterSmallFlat = imLayersAfterLargeFlat - imSmallFlatCut
            #****************************************************************
            # Check for ring structures
            #****************************************************************
            imLayersAfterSmallFlat = self.HandleRingStructures(imLayersAfterSmallFlat)
            imSmallBallCenter = imLayersAfterSmallFlat
            # Distance image for the small ball cutter
            imSmallBallDist = self.DISTANCE(imSmallBallCenter * 255)

            # Save images
            if Blender4CNC.DEBUG_DEPTH_IMAGES:
                # FAILS COVERAGE
                # imLayers is 0..1
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imLayers.png", imLayers * 255)
                # imLargeFlatCenter is 0..1
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imLargeFlatCenter.png", imLargeFlatCenter * 255)
                # imLargeFlatDist is 0..(max distance)
                # (which is why we do not multiply by 255 when saving
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imLargeFlatDist.png", imLargeFlatDist)
                # imLargeFlatCut is 0..1
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imLargeFlatCut.png", imLargeFlatCut * 255)
                # imLayersAfterLargeFlat is 0..1
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imLayersAfterLargeFlat.png", imLayersAfterLargeFlat * 255)
                # imSmallFlatCenter is 0..1
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imSmallFlatCenter.png", imSmallFlatCenter * 255)
                # imSmallFlatDist is 0..(max distance)
                # (which is why we do not multiply by 255 when saving
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imSmallFlatDist.png", imSmallFlatDist)
                # imSmallFlatCut is 0..1
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imSmallFlatCut.png", imSmallFlatCut * 255)
                # imLayersAfterSmallFlat is 0..1
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imLayersAfterSmallFlat.png", imLayersAfterSmallFlat * 255)
                # imSmallBallDist is 0..(max distance)
                # (which is why we do not multiply by 255 when saving
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imSmallBallDist.png", imSmallBallDist)
                #print("histogram imSmallBallDist=", numpy.histogram(imSmallBallDist,255))
                r,c = imSmallBallDist.shape
                imAll = numpy.zeros((r,c*imageCount))
                imAll[0:r, 0:c] = imLayers * 255
                imAll[0:r, c:c*2] = imLargeFlatCenter * 255
                if numpy.max(imLargeFlatDist) > 0:
                    imAll[0:r, c*2:c*3] = (imLargeFlatDist / numpy.max(imLargeFlatDist)) * 255
                else:
                    imAll[0:r, c*2:c*3] = imLargeFlatDist
                imAll[0:r, c*3:c*4] = imLargeFlatCut * 255
                imAll[0:r, c*4:c*5] = imLayersAfterLargeFlat * 255
                imAll[0:r, c*5:c*6] = imSmallFlatCenter * 255
                if numpy.max(imSmallFlatDist) > 0:
                    imAll[0:r, c*6:c*7] = (imSmallFlatDist / numpy.max(imSmallFlatDist)) * 255
                else:
                    imAll[0:r, c*6:c*7] = imSmallFlatDist
                imAll[0:r, c*7:c*8] = imSmallFlatCut * 255
                imAll[0:r, c*8:c*9] = imLayersAfterSmallFlat * 255
                if numpy.max(imSmallBallDist) > 0:
                    imAll[0:r, c*9:c*10] = (imSmallBallDist / numpy.max(imSmallBallDist)) * 255
                else:
                    imAll[0:r, c*9:c*10] = imSmallBallDist
                imageCount += 1
                Blender4CNC.GrayImages.SaveGrayPNG(imName + "-" + "%02d" % imageCount + "-imAll.png", imAll)

            #****************************************************************
            # Process the distance images for the roughing passes 
            #****************************************************************
            self.innerPathToleranceEnableCount = 0 # Start in G64 mode
            fname = self.filename + self.layername + "%s" + self.ext
            print("Processing GCode for Large Rough Cutter.")
            largeRoughGCode = self.GetGCodeForDistanceImage("", "", self.roughBitPixelRadius, len(self.listOfDepths), True, imLargeFlatDist, imLargeFlatCenter * 255)
            print("Processing GCode for Small Rough Cutter.")
            smallRoughGCode = self.GetGCodeForDistanceImage("", "", self.finalBitPixelRadius, 0, False, imSmallFlatDist, imSmallFlatCenter * 255)
            print("Processing GCode for Small Final Cutter.")
            finalRoughGCode = self.GetGCodeForDistanceImage("", "", self.finalBitPixelRadius, 0, False, imSmallBallDist, imLayersAfterSmallFlat * 255)
            finalRoughGCode = ["G61 (Disable Trajectory Blending)\n"] + finalRoughGCode

            #****************************************************************
            # Load in the image
            #****************************************************************
#            im = imA10Smooth * 255
            im = imA10Smooth

            # We flip the image because 0,0 is at top left, whereas in G-Code,
            # 0,0 is at bottom left
            im = numpy.flipud(im)
            
            #***************************************************************
            # Go through the smooth image one row at a time.
            # For each row, get the Z profile as a path, simplify it and
            # create the G-Code for it
            #****************************************************************
            finalGCode = []
            path = []
            # Because this is the first point, and given how GetGCodeForPointLiteralZ works,
            # we upset the last value of Y deliberately
            self.lastY = -1
            finalGCode.append(self.GetGCodeForPointLiteralZ(0, 0, self.i2g.rapid_height))
            print("Processing GCode for final pass.")
            #print("self.rows, self.cols=", self.rows, self.cols)
            for r in range(0,self.rows):
                path = []

                path.append("(Row " + str(r) + ", " + str(self.pixelInInches*r) + ")\n")
                
                # Zig-zag across image by rows
                if ((r % 2) == 1):
                    path.append(self.GetGCodeForPointActualZ_LastCol(self.cols-1, r, im[r,self.cols-1]))
                    c = self.cols-2
                    while (c >= 1):
                        # Add any point at which we detect a change in gradient
                        if ((im[r,c] - im[r,c+1]) != (im[r,c-1] - im[r,c])):
                            path.append(self.GetGCodeForPointActualZ(c, r, im[r,c]))
                        c -= 1
                    # Add in the last point
                    path.append(self.GetGCodeForPointActualZ(0, r, im[r,0]))
                else:
                    path.append(self.GetGCodeForPointActualZ(0, r, im[r,0]));
                    for c in range(1, (self.cols-1)):
                        # Add any point at which we detect a change in gradient
                        if ((im[r,c] - im[r,c-1]) != (im[r,c+1] - im[r,c])):
                            path.append(self.GetGCodeForPointActualZ(c, r, im[r,c]))
                    # Add in the last point
                    path.append(self.GetGCodeForPointActualZ_LastCol(self.cols-1, r, im[r,self.cols-1]))

                finalGCode += path
            # End for r    
            finalGCode.append(self.GetGCodeForSafeZ());

            fname = self.i2g.outBaseName
            self.WriteGCode(largeRoughGCode, fname + self.layername + "-1.ngc", self.i2g.rough_dia, "rough");
            self.WriteGCode(smallRoughGCode, fname + self.layername + "-2.ngc", self.i2g.final_dia, "rough");
            self.WriteGCode(finalRoughGCode, fname + self.layername + "-3.ngc", self.i2g.final_dia, "final");
            self.WriteGCode(finalGCode, fname + self.layername + "-4.ngc", -1, "");
            self.outFileNames.append(fname + self.layername + "-1.ngc")
            self.outFileNames.append(fname + self.layername + "-2.ngc")
            self.outFileNames.append(fname + self.layername + "-3.ngc")
            self.outFileNames.append(fname + self.layername + "-4.ngc")
        # End Go_Image2GCode_Layer        

        def DILATE(self, im, imOut, sz):
            k = self.GetDiscKernel(sz)
            scipy.ndimage.morphology.binary_dilation(im, structure=k, output=imOut)

        def DISTANCE(self, im):
            return scipy.ndimage.morphology.distance_transform_cdt(im, metric='chessboard', return_distances=True)

            # Put a white border around image
        def AddWhiteBorder(self, imA):
            x = imA.shape[0] + 2
            y = imA.shape[1] + 2
            imB = numpy.ones((x,y))
            imB *= 255
            imB[1:x-1, 1:y-1] = imA
            return imB

            # "Binify" layers and flatten
        def BinifyAndFlatten(self, imA16):
            images = []
            imA16X = copy.copy(imA16)
            for i in range(0, len(self.listOfDepths)):
                d = self.listOfDepths[i] / self.i2g.max_depth
                r1 = i*(self.rows+2)
                r2 = (i+1)*(self.rows+2)
                imA16X[r1:r2,:] *= d            
                images.append(imA16X[r1:r2,:])
            imC = copy.copy(images[0])
            for i in range(1,len(images)):
                imC = numpy.maximum(imC, images[i])
            imC = 1 - imC
            return imC

        #****************************************************************
        # Write the GCode paths to a file
        #****************************************************************
        def WriteGCode(self, paths, filename, cutter, rough):
            paths2 = []
            paths2 += self.GetGCodePreAmble(self.i2g.cutting_speed)
            paths2.append(self.GetGCodeForSafeZ())
            if (cutter > 0):
                paths2.append("M0 (Insert %0.2f %s cutter)\n" % (cutter,rough))
            paths2 += paths
            paths2 += self.GetGCodePostAmble()
            f = open(filename, "w")
            f.writelines(paths2)
            f.close()

        #****************************************************************
        # Given a grid string representing a list of lists 
        # (e.g. [ [0,1], [2,3] ] )
        # This will combine all large rough layers into one gcode file
        # with each layer placed as instructed in the grid list.
        # It will do the same combination for small rough layers, final
        # rough layers and final layers.
        #****************************************************************
        def CombineGCodeLayers(self, filename):
            # Get pre/post GCode
            preSize = len(self.GetGCodePreAmble(self.i2g.cutting_speed))
            postSize = len(self.GetGCodePostAmble()) + 1
        
            # Get step distances between layers    
            aspect = self.cols / self.rows
            carving_height = self.i2g.carving_width / aspect
            spacing = 0.5 # inches between each layer
            strideX = self.i2g.carving_width + spacing
            strideY = carving_height + spacing
            
            # For each cutting phase rough, small, final etc.
            for phase in range(1,5):
                l = []
                
                # For each layer L0,1,2...gather the gcode
                for i in range(0,self.i2g.number_layers):
                    fname = filename + "-L%d-%d.ngc" % (i, phase)
                    f = open(fname, "r")
                    lines = f.readlines()
                    # Chop off pre and post GCode
                    lines = lines[preSize:-postSize+1]
                    l.append(lines)
                    f.close()
                # End for each layer L0,1,2...

                # Combine the layers in a grid            
                l2 = []
                gridRowCount = -1
                grid = literal_eval(self.i2g.layers_grid)
                allRowImages = ""
                for gridRow in grid:
                    gridRowCount += 1
                    gridColCount = -1
                    rowImages = ""
                    for gridCol in gridRow:
                        gridColCount += 1
                        l2 += ["G92 X%d Y%d Z0\n" % (gridColCount * strideX, gridRowCount * strideY)]
                        l2 += l[gridCol]
                        l2 += ["G92 X%d Y%d Z0\n" % (-gridColCount * strideX, -gridRowCount * strideY)]
                        # Join the cut images together into a row
                        if (phase != 4):
                            if phase == 1:
                                toAdd = "-L%d-B16-LARGECUTX.png" % gridCol
                            elif phase == 2:
                                toAdd = "-L%d-B19-SMALLCUTX.png" % gridCol
                            elif phase == 3:
                                toAdd = "-L%d-B14-FINALCUTX.png" % gridCol
                            toAdd = filename + toAdd
                            if (rowImages == ""):
                                rowImages += toAdd
                            else:
                                rowImages += " " + toAdd
                        # End Join the cut images together into a row

                    # Actually do the join
                    if (phase != 4):
                        rowName = "image-B20-ROW%d.ext" % (gridRowCount+1)
                        l = rowImages.split(" ")
                        images = []
                        for name in l:
                            im = Blender4CNC.GrayImages.ReadGrayPNG(name)
                            images.append(im)
                        imA = numpy.hstack(tuple(images))
                        Blender4CNC.GrayImages.SaveGrayPNG(filename + "-B20-ROW%d.ext" % (gridRowCount+1), imA)

                        if (allRowImages == ""):
                            allRowImages = rowName
                        else:
                            # We reverse the order of the rows for display
                            allRowImages = rowName + " " + allRowImages
                    # End for gridCol in gridRow:

                # Now join rows to make grid
                if (phase != 4):
                    l = allRowImages.split(" ")
                    images = []
                    for name in l:
                        im = Blender4CNC.GrayImages.ReadGrayPNG(name)
                        images.append(im)
                    imA = numpy.vstack(tuple(images))
                    Blender4CNC.GrayImages.SaveGrayPNG(filename + "-B3%d-GRIDCUTX.ext" % (phase), imA)
                # End for gridRow in grid:

                # Write out the combined GCode
                fname = filename + "-Grid-%d.ngc" % phase
                if phase == 1:                
                    self.WriteGCode(l2, fname, self.i2g.rough_dia, "rough");
                if phase == 2:                
                    self.WriteGCode(l2, fname, self.i2g.final_dia, "rough");
                if phase == 3:                
                    self.WriteGCode(l2, fname, self.i2g.final_dia, "final");
                if phase == 4:                
                    self.WriteGCode(l2, fname, -1, "");
                    
            # End for each cutting phase rough, small, final etc.
        # End CombineGCodeLayers

        #*************************************************************************
        # Invert the black/white in the image
        # (Leave white border)
        #*************************************************************************
        def InvertImageLeaveBorder(self, im2):
            im2[:, 1:self.rows+1, 1:self.cols+1] -= 255
            im2[:, 1:self.rows+1, 1:self.cols+1] *= -1

        #*************************************************************************
        # A ring structure in the image (such as the rim of a volcano) can cause
        # problems as the algorithms will discover the outside edge of the blob
        # and cut half the material but will miss half the material because it
        # does not see that the blob has an "interior" edge. It does not handle
        # white space completely enclosed inside black space.
        #
        # This function looks for such structures and adds a tiny black line of
        # pixels through the ring (somewhere doesn't matter where). When the
        # algorithm follows the edge of the blob it will be drawn inside as well.
        #*************************************************************************
        def HandleRingStructures(self, imA):
            # Load in the image and make a copy of it for output
            #imName = "/home/d/My_Projects/CNC/cnc_designs/Metric_Test/RRR"
            #Blender4CNC.GrayImages.SaveGrayPNG(imName + "-Ring1.png", imA * 255)
            im = copy.copy(imA)
            
            #Blender4CNC.GrayImages.SaveGrayPNG("HandleRingStructures-inputImage.png", im)
            
            im = im.reshape((len(self.listOfDepths), self.rows+2, self.cols+2))
            im3 = copy.copy(im)

#            if self.rows+2 == 34:
#                for ij in range(0,32):
#                    print("AAAAAAAAAAAAAAA ", im3[0,ij,ij])
            
            #im3 = im3 - 255
            im3 = im3 - 1
            im3 = abs(im3)

            #imTemp = im3.reshape((len(self.listOfDepths)*(self.rows+2), self.cols+2))
            #Blender4CNC.GrayImages.SaveGrayPNG("HandleRingStructures-im3-again.png", imTemp)

            # Fill in the "background blob" (which is now foreground white)
            for z in range(0, len(self.listOfDepths)):
                self.FillBlob(im3, 1, 1, z, None)

            #imTemp = im3.reshape((len(self.listOfDepths)*(self.rows+2), self.cols+2))
            #Blender4CNC.GrayImages.SaveGrayPNG("HandleRingStructures-im3-filledbackground.png", imTemp)

            # Label any remaining blobs
            changed = False
            for z in range(0, len(self.listOfDepths)):
                labeled_array, num_features = scipy.ndimage.label(im3[z,:,:])
                objSlices = scipy.ndimage.find_objects(labeled_array)
                sliceCount = 0
                sliceLabel = 0
                for slice in objSlices:
                    sliceLabel += 1
                    changed = True
                    sliceRows = slice[0]
                    sliceCols = slice[1]
                    col = sliceCols.start
                    row = sliceRows.start
                    for row in range(sliceRows.start,sliceRows.stop-1):
                        for col in range(sliceCols.start,sliceCols.stop-1):
                            if labeled_array[row,col] == sliceLabel:
                                break
                        if labeled_array[row,col] == sliceLabel:
                            break

                    # On the original image, add a trench of black pixels to the SouthWest
                    cc = col
                    rr = row
                    while (im[z,rr,cc-1] != 0):
                        cc -= 1
                        im[z,rr,cc] = 0
                        rr -= 1
                        im[z,rr,cc] = 0
                
            # Save out the new image after disconnecting rings
            if (changed):
                im = im.reshape((len(self.listOfDepths)* (self.rows+2), self.cols+2))
                #Blender4CNC.GrayImages.SaveGrayPNG("HandleRingStructures-im-endHandleRingStructures.png", im)
                return im
            else:
                return imA
        # End HandleRingStructures

        #*************************************************************************
        # When doing multi-layer, "mountain tops" can get fully isolated from
        # supporting material around the edge - we need bridges to safely perform 
        # the cut without flinging around loose parts.
        # 
        # We handle this by finding ring structures on the lowest z-layer of all
        # but the base layers of the carving. We then add pixels of "bridge
        # material".
        #*************************************************************************
        def HandleMultiLayerOrphans(self, filename, finalName):
            # Load in the image and make a copy of it for output
            im = Blender4CNC.GrayImages.ReadGrayPNG(filename)
            im = im.reshape((len(self.listOfDepths), self.rows+2, self.cols+2))
            im2 = copy.copy(im)

            # Load in the image used for final GCode
            finalIm = Blender4CNC.GrayImages.ReadGrayPNG(finalName)
            
            self.InvertImageLeaveBorder(im2)

            # Fill in the "background blob" (which is now foreground white)
            for z in range(0, len(self.listOfDepths)):
                self.FillBlob(im2, 1, 1, z, None)

            # Any remaining black pixels must be part of isolated areas inside rings
            final1 = -self.layers[1]["MaxDepth"] + (self.finalBitRadius / 2)
            final2 = 0.1 + (self.finalBitRadius / 2)
            final3 = final2 / final1
            finalValue = int(final3 * 255)
            changed = False
            z = len(self.listOfDepths) - 2
            for r in range(0, (self.rows+1)):
                for c in range(0, (self.cols+1)):
                    if (im2[z,r,c] == 255):
                        # We have found an island!
                        changed = True
                        # Fill the island and return a center of the blob
                        center = self.FillBlobGetCenter(im2, c, r, z, None)
                        # Run bridges from center to all 4 edges
                        rr = int(center[1])
                        dist = int(0.125 / self.pixelInInches)
                        rr1 = rr - dist
                        rr2 = rr + dist
                        cc = int(center[0])
                        cc1 = cc - dist
                        cc2 = cc + dist
                        # Put row bridges from edge to edge
                        for cc in range(1, self.cols):
                            for rr in range(rr1,rr2):
                                im[z,rr,cc] = 0
                                if (finalIm[rr,cc] < finalValue):
                                    finalIm[rr,cc] = finalValue
                        # Put col bridges from edge to edge
                        for rr in range(1, self.rows):
                            for cc in range(cc1,cc2):
                                im[z,rr,cc] = 0
                                if (finalIm[rr,cc] < finalValue):
                                    finalIm[rr,cc] = finalValue
                    # End if
                # End for c
            # End for r
            
            # Save out the new image after disconnecting rings
            if (changed):
                im = im.reshape((len(self.listOfDepths)* (self.rows+2), self.cols+2))
                Blender4CNC.GrayImages.SaveGrayPNG(filename, im)
                Blender4CNC.GrayImages.SaveGrayPNG(finalName, finalIm)
        # End HandleMultiLayerOrphans

        #*************************************************************************
        # Uses a distance image and returns a list of paths (at all z levels) that
        # are separated by a value of "modulus". 
        # i.e. if modulus is 4, it will trace paths at 1, 5, 9, etc.
        #*************************************************************************
        def GetGCodeForDistanceImage(self, nameDist, nameBlobs, modulus, z, bottomUp, imIn = None, imBlobsIn = None):
            #print("GetGCodeForDistanceImage nameDist, nameBlobs, modulus, z, bottomUp, imIn.shape, imBlobsIn.shape=", nameDist, nameBlobs, modulus, z, bottomUp, imIn.shape, imBlobsIn.shape)
            # Load in the images
            if type(imIn) != type(None):
                im = imIn
#            else:
#                # FAILS COVERAGE
#                im = Blender4CNC.GrayImages.ReadGrayPNG(nameDist)
            if type(imBlobsIn) != type(None):
                imBlobs = imBlobsIn
#            else:
#                # FAILS COVERAGE
#                imBlobs = Blender4CNC.GrayImages.ReadGrayPNG(nameBlobs)

            # Because of the coordinate system, we want to flip each area
            im = numpy.flipud(im)
            imBlobs = numpy.flipud(imBlobs)
            
            # Reshape to 3D
            im = im.reshape((len(self.listOfDepths), self.rows+2, self.cols+2))
            imBlobs = imBlobs.reshape((len(self.listOfDepths), self.rows+2, self.cols+2))
            
            # Starting search point is lower-left (0,0) for machine 
            # (1,1) to be inside boundary
            if (bottomUp):
                ret = self.GetGCodeForImageBottomUp(im, imBlobs, modulus, 0, 1, 1);
            else:
                ret = self.GetGCodeForImageTopDown(im, imBlobs, modulus, len(self.listOfDepths)-1, 1, 1);
            return ret
        # End GetGCodeForDistanceImage
        
        #*************************************************************************
        # Start at the deepest z level and cut nested blobs working our way up to 
        # the highest level. The paths are stacked in reverse discovery so that
        # the higher depths are cut first but this approach lets us nest blobs
        # that are together (used only during first roughing pass). 
        #*************************************************************************
        def GetGCodeForImageBottomUp(self, im, imBlobs, modulus, z, startX, startY):
            path = []
            prePath = []
            midPath = []
            bigPath = []
            while (True):
                # Find the next blob at this level given the starting point
                curPixel = self.FindNextBlob(imBlobs, Blender4CNC.MyPix(startX, startY, 0, 0), z)
                # If 0,0 is returned then there are no blobs to find!
                if (curPixel.x == 0):
                    # Have we finished all layers, if not move up one layer
                    if (z >= (len(self.listOfDepths)-1)):
                        break
                    z += 1
                    continue

                # Erase the current blob (from future searches)
                self.FillBlob(imBlobs, curPixel.x, curPixel.y, z, None)

                prePath = []
                midPath = []
                path = []
                # Rapid to this blob at previous z level
                prePath.append(self.GetGCodeForRapidPoint(curPixel.x, curPixel.y))
                nextline = self.GetGCodeForPoint(curPixel.x, curPixel.y, z)
                prePath.append(nextline)
                # Get the path to cut this at this level
                midPath += self.GetGCodeForThisBlob(im, modulus, z, curPixel)

                # When going bottom-up, all lower levels will check if a blob exists on the level above
                if ((z < (len(self.listOfDepths)-1)) and (imBlobs[z+1, curPixel.y, curPixel.x] == self.fgnd)):
                    # There is a blob above, so find the edge of it (just go N)
                    upPixel = copy.copy(curPixel)
                    while (imBlobs[z+1,upPixel.y+1,upPixel.x] != self.bgnd):
                        upPixel.y += 1
                    # We now have an edge pixel on the blob on the level above
                    path2 = self.GetGCodeForImageBottomUp2(im, imBlobs, modulus, z+1, upPixel.x, upPixel.y)
                    # Remove the command at the end to raise to safe Z level
                    path2 = path2[:-1]
                    # We must PREPEND this upper path before the current level
                    path = []
                    path += path2
                    path.append(self.GetGCodeForRapidPoint(curPixel.x, curPixel.y))
                    path.append(self.GetGCodeForPoint(curPixel.x, curPixel.y, z))
                    path += midPath
                else:
                    path += prePath
                    path += midPath
                # End if ((z < (len(...

                path.append(self.GetGCodeForSafeZ())

                bigPath += path

                # OK, the blob that was found has been cut AND any blobs ABOVE it were cut and
                # prepended so now we reset the starting point and go around again to find
                # any more blobs on this level
                startX = curPixel.x
                startY = curPixel.y
            # End while
            return bigPath;
        # End GetGCodeForImageBottomUp

        def GetGCodeForImageBottomUp2(self, im, imBlobs, modulus, z, startX, startY):
            path = []

            curX = startX
            curY = startY

            # Erase the current blob (from future searches)
            self.FillBlob(imBlobs, curX, curY, z, None)

            # Rapid to this blob at previous z level
            path.append(self.GetGCodeForRapidPoint(curX, curY))
            path.append(self.GetGCodeForPoint(curX, curY, z))
            # Get the path to cut this at this level
            curPixel = Blender4CNC.MyPix(startX, startY, 1, 0)
            path += self.GetGCodeForThisBlob(im, modulus, z, curPixel)

            # When going bottom-up, all lower levels will check if a blob exists on the level above
            BGND = self.bgnd
            if (z < (len(self.listOfDepths)-1)):
                if (imBlobs[z+1, curY, curX] == self.fgnd):
                    # There is a blob above, so find the edge of it (just go N)
                    upX = curX
                    upY = curY
                    while (imBlobs[z+1,upY+1,upX] != BGND):
                        upY += 1
                    # We now have an edge pixel on the blob on the level above
                    path2 = self.GetGCodeForImageBottomUp2(im, imBlobs, modulus, z+1, upX, upY)
                    # Remove the command at the end to raise to safe Z level
                    path2 = path2[:-1]
                    # We must PREPEND this upper path before the current level
                    path2 += path
                    path = []
                    path += path2
                # End if (imBlobs[z11,
            # End if (z > 0):

            path.append(self.GetGCodeForSafeZ())

            # OK, the blob that was found has been cut AND any blobs ABOVE it were cut 
            return path
        # End GetGCodeForImageBottomUp2

        #*************************************************************************
        def FillBlob(self, im, startX, startY, z, fn):
            imZ2 = im[z,:,:]
            #imTemp = im3.reshape((len(self.listOfDepths)*(self.rows+2), self.cols+2))
            #Blender4CNC.GrayImages.SaveGrayPNG("FillBlob-a.png", imZ2)
            skimage.morphology.flood_fill(imZ2, (startY, startX), self.bgnd, connectivity=1, in_place=True)
            #Blender4CNC.GrayImages.SaveGrayPNG("FillBlob-b.png", imZ2)
        #*************************************************************************
        # Flood fill a blob - setting all its pixels to background
        # Find and return the "Center" of the blob (half way between min/max x,y)
        # This is about 20% faster than having a single list and checking all 4 
        # directions at each pixel
        #*************************************************************************
        def FillBlobGetCenter(self, im, startX, startY, z, fn):
            valu = im[z,startY,startX]
            BGND = self.bgnd
            im[z,startY,startX] = self.bgnd	# Clear the start pixel

            xsLR = [startX]
            ysLR = [startY]
            xsUD = [startX]
            ysUD = [startY]

            imZ = im[z,:,:]

            i = 0
            ii = 0
            while (i < len(xsLR)) or (ii < len(xsUD)):
                while i < len(xsLR):
                    X = xsLR[i]
                    Y = ysLR[i]

                    # Check all along to the right until we hit an edge of blob
                    Xj = X + 1
                    while imZ[Y,Xj] == valu:
                        imZ[Y,Xj] = BGND
                        xsUD.append(Xj)
                        ysUD.append(Y)
                        Xj += 1
                    # Check all along to the left until we hit an edge of blob
                    Xj = X - 1
                    while imZ[Y,Xj] == valu:
                        imZ[Y,Xj] = BGND
                        xsUD.append(Xj)
                        ysUD.append(Y)
                        Xj -= 1
                    i += 1        
                            
                while ii < len(xsUD):
                    X = xsUD[ii]
                    Y = ysUD[ii]

                    # Check all along to the top until we hit an edge of blob
                    Yj = Y + 1
                    while imZ[Yj,X] == valu:
                        imZ[Yj,X] = BGND
                        xsLR.append(X)
                        ysLR.append(Yj)
                        Yj += 1
                    # Check all along to the bottom until we hit an edge of blob
                    Yj = Y - 1
                    while imZ[Yj,X] == valu:
                        imZ[Yj,X] = BGND
                        xsLR.append(X)
                        ysLR.append(Yj)
                        Yj -= 1
                    ii += 1                
                
            im[z,:,:] = imZ

            minY = min(ysLR)
            maxY = max(ysLR)
            minX = min(xsUD)
            maxX = max(xsUD)
            # Return the "center" of the blob
            return (minX+(maxX-minX)/2, minY+(maxY-minY)/2)
        # End FillBlob
        
        #*************************************************************************
        # Returns True if the current blob is 3 pixels or smaller
        #*************************************************************************
        def IsTinyBlob(self, im, startX, startY, z):
            pixels2 = [Blender4CNC.MyPix(startX,startY,0,1)]
            valu = im[z,startY,startX]

            while (len(pixels2) > 0):

                addedSomething = False
                endi = len(pixels2)
                for i in range(0, endi):
                    p = pixels2[i]

                    # Check all 4 directions for any touching fgnd pixels
                    for j in range(0,4):
                        if (im[z,p.y+p.dy,p.x+p.dx] == valu): 
                            # We have found a fgnd pixel
                            # See if it is already in our list before adding it
                            found = False
                            for k in range(0, len(pixels2)):
                                pp = pixels2[k]
                                if (pp.x == (p.x+p.dx)) and (pp.y == (p.y+p.dy)):
                                    found = True 
                                    break
                            if not found:
                                # Not in list already, so add it
                                pixels2.append(Blender4CNC.MyPix(p.x+p.dx,p.y+p.dy,0,1))
                                addedSomething = True
                        p.Rotate90CW()
                    # End for j
                # End for i
                if (len(pixels2) >= 3):
                    return False
                if not addedSomething:
                    return True
            # End while
            return True
        # End FillBlob

        #*************************************************************************
        # Determine a suitable direction
        #*************************************************************************
        def DetermineSuitableDirection(self, im, z, r, c):
            if (im[z,r,c-1] == self.bgnd):
                return Blender4CNC.MyPix(c,r,1,0) # East
            if (im[z,r+1,c] == self.bgnd):
                return Blender4CNC.MyPix(c,r,0,-1) # South
            if (im[z,r,c+1] == self.bgnd):
                return Blender4CNC.MyPix(c,r,-1,0) # West
            return Blender4CNC.MyPix(c,r,0,1) # North
        #*************************************************************************
        # From a starting point, use an expanding rectangular area to find the 
        # closest blob of the foreground color
        #*************************************************************************
        def FindNextBlob(self, im, startPixel, z):
            rect = []
            for i in range(0,4):
                rect.append(Blender4CNC.MyPix(0,0,0,0))

            # Remember if a corner is on the edge
            stepX = (0,-1,0,1)
            stepY = (-1,0,1,0)
            leftEdge = False
            rightEdge = False
            topEdge = False
            bottomEdge = False

            # Create a rectangle as 4 corners	
            rect[0] = Blender4CNC.MyPix(startPixel.x+1, startPixel.y+1, 1, 1)
            rect[1] = Blender4CNC.MyPix(startPixel.x+1, startPixel.y-1, 1, -1)
            rect[2] = Blender4CNC.MyPix(startPixel.x-1, startPixel.y-1, -1, -1)
            rect[3] = Blender4CNC.MyPix(startPixel.x-1, startPixel.y+1, -1, 1)

            # Keep checking and expanding the rectangle until we find a blob
            # (or cover the whole image)
            COLS_PLUS_1 = self.cols+1
            ROWS_PLUS_1 = self.rows+1
            FGND = self.fgnd
            while ((not leftEdge) or (not rightEdge) or (not topEdge) or (not bottomEdge)):
                # Check all 4 edges for a blob pixel
                if rect[0].x < COLS_PLUS_1:
                    c = rect[0].x
                    r = rect[0].y
                    THE_END = rect[1].y
                    su = numpy.sum(im[z,THE_END+1:r,c])
                    if su > 0:
                        while (r != THE_END):
                            if (im[z,r,c] == FGND): # We have found a blob
                                return self.DetermineSuitableDirection(im, z, r, c)
                            r -= 1
                if rect[1].y > 0:
                    c = rect[1].x
                    r = rect[1].y
                    THE_END = rect[2].x
                    su = numpy.sum(im[z,r,THE_END+1:c])
                    if su > 0:
                        while (c != THE_END):
                            if (im[z,r,c] == FGND): # We have found a blob
                                return self.DetermineSuitableDirection(im, z, r, c)
                            c -= 1
                if rect[2].x > 0:
                    c = rect[2].x
                    r = rect[2].y
                    THE_END = rect[3].y
                    su = numpy.sum(im[z,r:THE_END-1,c])
                    if su > 0:
                        while (r != THE_END):
                            if (im[z,r,c] == FGND): # We have found a blob
                                return self.DetermineSuitableDirection(im, z, r, c)
                            r += 1
                if rect[3].y < ROWS_PLUS_1:
                    c = rect[3].x
                    r = rect[3].y
                    THE_END = rect[0].x
                    su = numpy.sum(im[z,r,c:THE_END-1])
                    if su > 0:
                        while (c != THE_END):
                            if (im[z,r,c] == FGND): # We have found a blob
                                return self.DetermineSuitableDirection(im, z, r, c)
                            c += 1

                # Move corners out
                for i in range(0,4):
                    rect[i].MoveInDirection()

                    # Make sure all 4 corners are inside image edges
                    rect[i].x = self.clamp(rect[i].x, 0, self.cols+1)
                    rect[i].y = self.clamp(rect[i].y, 0, self.rows+1)

                    # Check if on edge
                    leftEdge = leftEdge or (rect[i].x <= 0)
                    rightEdge = rightEdge or (rect[i].x >= self.cols+1)
                    topEdge = topEdge or (rect[i].y >= self.rows+1)
                    bottomEdge = bottomEdge or (rect[i].y <= 0)
                # End for i in range(0,4):
            # End while (!leftEdge or !rightEdge or !topEdge or !bottomEdge):
            return Blender4CNC.MyPix(0,0,0,0)

        #*************************************************************************
        # Start at the highest z level and cut blobs working our way down to the 
        # deepest level (used for all but the first roughing pass).
        #*************************************************************************
        def GetGCodeForImageTopDown(self, im, imBlobs, modulus, z, startX, startY, infiniteLoopCounter = 10000):
            path = []
            
            count = 0
            while (True):
                count += 1
                if (count > infiniteLoopCounter):
                    str2 = "ERROR - GetGCodeForImageTopDown seems to be stuck in infinite while loop?"
                    raise Exception(str2)
                # Find the next blob at this level given the starting point
                curPixel = self.FindNextBlob(imBlobs, Blender4CNC.MyPix(startX, startY, 0, 0), z)
                # If 0,0 is returned then there are no blobs to find!
                if (curPixel.x == 0):
                    # Have we finished all layers, if not move down one layer
                    if (z <= 0):
                        break
                    z -= 1
                    continue

                # When going top-down we are on the 2nd and 3rd phases and we ignore 
                # really tiny blobs
                tiny = self.IsTinyBlob(imBlobs, curPixel.x, curPixel.y, z)

                # Erase the current blob (from future searches)
                self.FillBlob(imBlobs, curPixel.x, curPixel.y, z, None)
    
#                imBlobs2 = imBlobs.reshape((len(self.listOfDepths) * (self.rows+2), self.cols+2))
#                Blender4CNC.GrayImages.SaveGrayPNG(self.filename + "-imBlobs" + str(count) + self.ext, imBlobs2)


#                imX = copy.copy(im)
#                imX *= 255
#                imX[z, curPixel.y, curPixel.x] = 127
#                imX[z, 36, 44] = 127
#                imX2 = imX.reshape((len(self.listOfDepths) * (self.rows+2), self.cols+2))
#                Blender4CNC.GrayImages.SaveGrayPNG(self.filename + "-imXs" + str(count) + self.ext, imX2)
                
                
                if tiny:
                    continue
                
                # If the next blob is really close to the previous blob, we are going to eliminate the
                # rapid movement to safe Z that is at the end of the previous blob
                if (math.sqrt(self.getDistanceSqrd(startX, startY, curPixel.x, curPixel.y)) <= (self.finalBitPixelRadius*2)):
                    #print("REMOVING")
                    path = path[:-1]

                # Rapid to this blob at previous z level
                path.append(self.GetGCodeForRapidPoint(curPixel.x, curPixel.y))
                path.append(self.GetGCodeForPoint(curPixel.x, curPixel.y, z))
                # Get the path to cut this at this level
                path += self.GetGCodeForThisBlob(im, modulus, z, curPixel)

                path.append(self.GetGCodeForSafeZ())

                # Go around again to find any more blobs on this level
                startX = curPixel.x
                startY = curPixel.y
            # End while
            return path
        # End GetGCodeForImageTopDown

        #*************************************************************************
        # Return value in proper range
        #*************************************************************************
        def clamp(self, n, smallest, largest): 
            return max(smallest, min(n, largest))

        #*************************************************************************
        # From a starting point on the edge of a blob, generate the G code to cut
        # this blob
        #*************************************************************************
        def GetGCodeForThisBlob(self, im, modulus, z, curPixel, recursionDepth=0, infiniteLoopCounter = 100000, recursionDepthLimit = 5000):
            # Get the ring we are on
            valu = im[z, curPixel.y, curPixel.x]
            
            # Get starting pattern (to know when to exit)
            startPix = copy.copy(curPixel)
            startPix2 = self.GetPix(im, startPix, valu, z)
            
            # Add start pixel to GCode path
            path = []
            path.append(self.GetGCodeForPoint(startPix.x, startPix.y, z))

            modulusInt = int(modulus)
            if modulusInt == 0:
                # For example, maybe modulus2 = 0.5 and the int() of that becomes 0 -> leads to infinite recursion
                modulusInt = 1
            
            # Create the snake
            snake = [startPix, startPix2]
            self.InnerPathMaxRow = self.rows+2
            self.InnerPathMaxCol = self.cols+2
            
            count = 0
            while (True):
                count += 1
                if (count > infiniteLoopCounter):
                    str2 = "ERROR - GetGCodeForThisBlob seems to be stuck in infinite while loop?"
                    raise Exception(str2)
                if (recursionDepth > recursionDepthLimit):
                    str2 = "ERROR - GetGCodeForThisBlob seems to be stuck in infinite recursion?"
                    raise Exception(str2)

                # Handle the case where this pixel can move to an inner path
                tp = self.CheckForInnerPath(im, snake[-1], valu, modulusInt, z)

                if (tp.x != -1):
                    # Move to the head
                    s = self.GetGCodeForPoint(snake[-1].x, snake[-1].y, z)
                    if (s != ''):
                        path.append(s)
                    # Chop off the tail
                    snake = [snake[-1]]
                    
                    # An an optimization at machine runtime, inner paths can be inaccurate so we
                    # use path blending with wider tolerances
                    tol = self.pixelInInches * modulus / 4
                    if (self.innerPathToleranceEnableCount == 0):
                        # This must be the "first" inner path on this blob
                        if (bpy.context.scene.unit_settings.system == "METRIC"):
                            path += ["G64 P%0.4f Q%0.4f\n" % (tol * 1000, tol * 1000)]
                        else:
                            path += ["G64 P%0.4f Q%0.4f\n" % (tol, tol)]
                    self.innerPathToleranceEnableCount += 1
                    
                    # Get inner path
                    path += ["(Going In)\n"]
                    path += self.GetGCodeForThisBlob(im, modulus, z, tp, recursionDepth+1)
                    path += ["(Going Out)\n"]

                    # Switch back from optimization
                    self.innerPathToleranceEnableCount -= 1
                    if (self.innerPathToleranceEnableCount == 0):
                        # This must be the "first" inner path on this blob
                        path += ["G64\n"]                 
                    
                    # Clear inner path
                    self.FillBlob(im, tp.x, tp.y, z, None)
                    # Move to the head (from inner path)
                    path.append(self.GetGCodeForPoint(snake[-1].x, snake[-1].y, z))
                # End if inner path
                else:
                    # Have we changed direction?
                    if (not snake[-1].IsDirectionEqual(snake[-2])):
                        # Move to the neck
                        s = self.GetGCodeForPoint(snake[-2].x, snake[-2].y, z)
                        if (s != ''):
                            path.append(s)

                        # Chop off the tail
                        snake = [snake[-1]]
                # End else (not inner path)
                
                # Get next pixel (stretch snake forward)
                snake.append(self.GetPix(im, snake[-1], valu, z))
                
                # Have we reached the starting pattern ?
                if (snake[-1].IsLocationEqual(startPix2)) and (snake[-2].IsLocationEqual(startPix)):
                    break
            # End while                    
            
            # Move to the neck
            s = self.GetGCodeForPoint(snake[-2].x, snake[-2].y, z)
            if (s != ''):
                path.append(s)
            # End GetGCodeForThisBlob
            return path

        #*************************************************************************
        # From the current pixel/dir, determine if there is an inner path - if so,
        # return the inner pixel in tp
        #*************************************************************************
        def CheckForInnerPath(self, im, p, valu, modulus, z):
            tp = Blender4CNC.MyPix(-1,0,p.dx,p.dy)
            pdx = p.dx
            pdy = p.dy
            px = p.x
            py = p.y

            # Look for an inner path - we look right and diagonally right
            # It is possible for right to go out of the image bounds
#            inRight = False
            pdxm = pdx * modulus
            pdym = pdy * modulus
            if (((py - pdxm) < (self.InnerPathMaxRow)) and ((px + pdym) < (self.InnerPathMaxCol))):
                inRight = im[z, py - pdxm, px + pdym]
                # Do we have an inner path ?
                if (inRight == (valu + modulus)): 
                    tp.x = px + pdym
                    tp.y = py - pdxm
                    return tp
            
                # It is possible for the forward diagonal to go out of the image bounds
#                inDiagRight = False
                if (((py + pdym - pdxm) < (self.InnerPathMaxRow)) and ((px + pdxm + pdym) < (self.InnerPathMaxCol))):
                    inDiagRight = im[z, py + pdym - pdxm, px + pdxm + pdym]
                    # Do we have an inner path ?
                    if (inDiagRight == (valu + modulus)): 
                        tp.x = px + (pdxm + pdym)
                        tp.y = py + (pdym - pdxm)
                        return tp
            return tp

        #*************************************************************************
        # Given a current pixel and direction, checks in all 4 directions
        # and returns the position of the next pixel of same value
        # e.g. im.shape = (1,7,7)
        # [[[0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 1, 1, 1, 0, 0],
        #   [0, 0, 1, 0, 1, 0, 0],
        #   [0, 0, 1, 1, 1, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0]]]
        # e.g. Pixel at im[0,2,3] (y/row=2, col/x=3)
        # e.g. direction at dx=1, dy=0 (East)
        # [[[0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 0, P, d, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0],
        #   [0, 0, 0, 0, 0, 0, 0]]]
        # e.g. This function will flip the direction to West, then rotate 90 deg.
        # checking at each point - N, E, S, W
        #*************************************************************************
        def GetPix(self, im, pp, valu, z):
            pdy = -pp.dy # Rotate 180
            pdx = -pp.dx
            for i in range(0,4):
                t = pdy # Rotate 90 CW
                pdy = -pdx
                pdx = t
                if (im[z, (pp.y + pdy), (pp.x + pdx)] == valu):
                    return Blender4CNC.MyPix(pp.x + pdx, pp.y + pdy, pdx, pdy)
            return Blender4CNC.MyPix(pp.x, pp.y, pdx, pdy)

        #*****************************************************************
        # Get the GCode startup code that goes at the start of the program 
        #*****************************************************************
        def GetGCodePreAmble(self, cuttingSpeed):
            list = [e + "\n" for e in self.i2g.gcodePreAmble]
            list.append("F%d\n" % cuttingSpeed)
            return list

        #***************************************************
        # Get the GCode that goes at the end of the program
        #***************************************************
        def GetGCodePostAmble(self):
            list = [e + "\n" for e in self.i2g.gcodePostAmble]
            return list

        #*************************************************************************
        # GCode for popping up to a safe Z height (out of the material)
        #*************************************************************************
        def GetGCodeForSafeZ(self):
            self.lastZ = self.i2g.rapid_height # -100
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return "G0 Z%0.3f\n" % (self.i2g.rapid_height * 1000)
            else:
                return "G0 Z%0.3f\n" % self.i2g.rapid_height

        #*************************************************************************
        # GCode for moving rapidly to the next blob to cut
        #*************************************************************************
        def GetGCodeForRapidPoint(self, x, y):
            x -= 1
            y -= 1
            self.lastX = x
            self.lastY = y
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                return "G0 X%0.3f Y%0.3f\n" % (self.GetX(x) * 1000, self.GetY(y) * 1000)
            else:
                return "G0 X%0.3f Y%0.3f\n" % (self.GetX(x), self.GetY(y))

        #*************************************************************************
        # 
        #*************************************************************************
        def GetX(self, x):
            return x * self.pixelInInches + self.i2g.offset_x;
        def GetX_LastCol(self, x):
            return self.i2g.carving_width + self.i2g.offset_x;
        def GetY(self, y):
            return y * self.pixelInInches + self.i2g.offset_y;

        #*************************************************************************
        # GCode for moving to the next point - the z value represents the 
        # ACTUAL depth as an amount of the max depth
        # This is ONLY called when doing the final phase
        #*************************************************************************
        def GetGCodeForPointActualZ(self, x, y, z):
            return self.GetGCodeForPointLiteralZ(x, y, ((((float)(self.MAX_PIXEL_VALUE)-z)/self.MAX_PIXEL_VALUE) * self.i2g.max_depth))
        def GetGCodeForPointActualZ_LastCol(self, x, y, z):
            return self.GetGCodeForPointLiteralZ_LastCol(x, y, ((((float)(self.MAX_PIXEL_VALUE)-z)/self.MAX_PIXEL_VALUE) * self.i2g.max_depth))

        #*************************************************************************
        # GCode for moving to the next point - the z value is exact 
        # This is ONLY called when doing the final phase
        #*************************************************************************
        def GetGCodeForPointLiteralZ(self, x, y, z):
            s = "G1"
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                s += " X%0.3f" % (self.GetX(x) * 1000)
                if (self.lastY != y):    
                    s += " Y%0.3f" % (self.GetY(y) * 1000)
                s += " Z%0.3f\n" % (z * 1000)
            else:
                s += " X%0.3f" % self.GetX(x)
                if (self.lastY != y):    
                    s += " Y%0.3f" % self.GetY(y)
                s += " Z%0.3f\n" % z
            self.lastY = y
            return s
        def GetGCodeForPointLiteralZ_LastCol(self, x, y, z):
            s = "G1"
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                s += " X%0.3f" % (self.GetX_LastCol(x) * 1000)
                if (self.lastY != y):    
                    s += " Y%0.3f" % (self.GetY(y) * 1000)
                s += " Z%0.3f\n" % (z * 1000)
            else:
                s += " X%0.3f" % self.GetX_LastCol(x)
                if (self.lastY != y):    
                    s += " Y%0.3f" % self.GetY(y)
                s += " Z%0.3f\n" % z
            self.lastY = y
            return s

        #*************************************************************************
        # GCode for moving to the next point - the z value represents a level in 
        # the list of roughing depths
        #
        # This is ONLY called when doing the rough phases
        #*************************************************************************
        def GetGCodeForPoint(self, x, y, z):
            s = "G1"
            # The images used for roughing have a buffer of one pixel around the borders
            # Therefore we need to subtract 1 from each coordinate 
            x -= 1
            y -= 1
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                if (x != self.lastX):
                    s += " X%0.3f" % (self.GetX(x) * 1000)
                if (y != self.lastY):
                    s += " Y%0.3f" % (self.GetY(y) * 1000)
                if (self.listOfDepths[-z-1] != self.lastZ):
                    s += " Z%0.3f" % (self.listOfDepths[-z-1] * 1000)
            else:
                if (x != self.lastX):
                    s += " X%0.3f" % self.GetX(x)
                if (y != self.lastY):
                    s += " Y%0.3f" % self.GetY(y)
                if (self.listOfDepths[-z-1] != self.lastZ):
                    s += " Z%0.3f" % self.listOfDepths[-z-1]
            self.lastX = x
            self.lastY = y
            self.lastZ = self.listOfDepths[-z-1]
            if (s == "G1"): # If nothing changed, just have empty line
                s = ""
            else:
                s += "\n"
            return s

        #*************************************************************************
        # Create a circular kernel to be used with grayscale dilation
        #*************************************************************************
        def GetKernel(self, radius):
            # The z axis has a different resolution compared to the X and Y
            # So a spherical cutter must be "warped" to an ellipsoid shape in the math
            m = (256 / (-self.i2g.max_depth)) * self.pixelInInches

            r = round(radius)
            mid = r
            size = mid*2 + 1
            k = numpy.zeros((size,size))
            k[:,:] = self.MAX_PIXEL_VALUE

            r2 = radius * radius
            for i in range(0, size):
                for j in range(0, size):
                    d = self.getDistanceSqrd(mid,mid,i,j)
                    if (d <= r2):
                        k[i,j] = m * (radius - math.sqrt(r2 - d))
            return k
        # End GetKernel

        #*************************************************************************
        # Create a disc kernel to be used with binary dilation
        #*************************************************************************
        def GetDiscKernel(self, radius):
            # Generate a quarter
            r = ceil(radius) + 1
            r2 = radius**2
            k = numpy.zeros((r,r))
            for x in range(0,r):
                for y in range(0,r):
                    d = x**2 + y**2
                    if d <= r2:
                        k[x,y] = 1
            # Mirror to create half
            k2 = k[1:,]
            k2 = numpy.flip(k2,0)
            k2 = numpy.vstack((k2,k))
            # Mirror to create whole
            k3 = k2[:,1:]
            k3 = numpy.flip(k3,1)
            k3 = numpy.hstack((k3,k2))
            # If nothing in outer band, reduce array to save computations
            sz = r * 2 - 1
            if sum(k3[0,:]) == 0:
                k3 = k3[1:sz-1,1:sz-1]
            return k3
        # End GetKernel

        #*************************************************************************
        # Get the squared distance between 2 points
        #*************************************************************************
        def getDistanceSqrd(self, x1, y1, x2, y2):
            x = x2-x1
            y = y2-y1
            return x*x + y*y

        #******************************************************************
        # Calculate parameters for the user parameters
        #******************************************************************
        def GetCalculatedParams(self):
            (self.cols, self.rows) = self.GetImageDimensions(self.i2g.file_name)

            self.finalBitRadius = self.i2g.final_dia / 2
            self.roughBitPixelDiameter = (int)(self.i2g.rough_dia / self.i2g.ystep)
            self.finalBitPixelDiameter = (int)(self.i2g.final_dia / self.i2g.ystep)
            self.roughBitPixelRadius = self.roughBitPixelDiameter / 2
            self.finalBitPixelRadius = self.finalBitPixelDiameter / 2

            finalRoughZDepth = self.i2g.max_depth + (self.finalBitRadius / 2)

            self.filename = os.path.splitext(self.i2g.file_name)[0]
            self.ext = os.path.splitext(self.i2g.file_name)[1]
            
            # Get a list of cutting depths for layer 0
            self.layer0Depths = []
            d = finalRoughZDepth
            while d < 0: 
                self.layer0Depths.append(d)
                d -= float(self.i2g.zstep)
            self.layer0Depths.reverse()

            self.layerNDepths = []

            self.MAX_PIXEL_VALUE = 255;
            self.fgnd = self.MAX_PIXEL_VALUE
            self.bgnd = 0
            
            layers = []
            layers.append({})
            layers[0]["MaxDepth"] = self.i2g.max_depth
            layers[0]["MinPixel"] = 0
            layers[0]["MaxPixel"] = self.MAX_PIXEL_VALUE
                
            # If we are doing laminations
            if (self.i2g.number_layers > 1):
                bottomMaterial = (self.i2g.laminate_thickness * self.i2g.number_layers) + self.i2g.max_depth
                zPixelsPerInch = -(float)(self.MAX_PIXEL_VALUE) / self.i2g.max_depth
                zPixelsPerRadius = zPixelsPerInch * self.finalBitRadius

                layers[0]["MaxDepth"] = -(self.i2g.laminate_thickness - bottomMaterial)
                layers[0]["MaxValue"] = (int)(zPixelsPerInch * (-layers[0]["MaxDepth"]))
                layers[0]["MinPixel"] = 0
                layers[0]["MaxPixel"] = layers[0]["MaxValue"]
                if (layers[0]["MaxPixel"] >= self.MAX_PIXEL_VALUE):
                    # FAILS COVERAGE
                    layers[0]["MaxPixel"] = self.MAX_PIXEL_VALUE-1

                for i in range(1, self.i2g.number_layers):
                    layers.append({})
                    layers[i]["MaxDepth"] = -(self.i2g.laminate_thickness + self.finalBitRadius)
                    layers[i]["MaxValue"] = (int)(zPixelsPerInch * (-layers[i]["MaxDepth"]))
                    layers[i]["MinPixel"] = (int)(layers[i-1]["MaxPixel"] - zPixelsPerRadius)
                    layers[i]["MaxPixel"] = layers[i]["MinPixel"] + layers[i]["MaxValue"]
                    if (layers[i]["MaxPixel"] >= self.MAX_PIXEL_VALUE):
                        layers[i]["MaxPixel"] = self.MAX_PIXEL_VALUE-1

                # Get a list of cutting depths for layer 0
                final = layers[0]["MaxDepth"] + (self.finalBitRadius / 2)
                layer0Depths = []
                d = final
                while d < 0: 
                    layer0Depths.append(d)
                    d -= float(self.i2g.zstep)
                layer0Depths.reverse()
                self.layer0Depths = layer0Depths

                # Get a list of cutting depths for other layers
                final = layers[1]["MaxDepth"] + (self.finalBitRadius / 2)
                layerNDepths = []
                d = final
                while d < 0: 
                    layerNDepths.append(d)
                    d -= float(self.i2g.zstep)
                layerNDepths.reverse()
                self.layerNDepths = layerNDepths
            # End if (myParams["NumberLayers"] > 1)
            self.layers = layers 
        # End GetCalculatedParams(self)
           
        #******************************************************************
        # Get image dimensions
        #******************************************************************
        def GetImageDimensions(self, filenameIn):
            # Remove image if it exists         
            filename = bpy.path.basename(filenameIn)
            wasLoaded = False
            if filename in bpy.data.images.keys():
                img = bpy.data.images[filename]
            else:
                img = bpy.data.images.load(filenameIn)
                wasLoaded = True
            (width, height) = img.size
            if wasLoaded:
                bpy.data.images.remove(img)
            return [width, height]
        
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A class to represent a CNC machine for use by GCodeMachine
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS TheMachine
    class TheMachine:
    
        #COVERAGE_CLASS TheMachine
        def __init__(self):
            self.bank0X = 0.0
            self.bank0Y = 0.0
            self.bank0Z = 0.0
            self.bank1X = 0.0
            self.bank1Y = 0.0
            self.bank1Z = 0.0
            self.mode1 = "G0"
            self.GlobalParameters = {}
            self.Parameters30 = {}
            self.LocalNamedParameters = {}
            self.units = None
            self.drillCycleRValue = 0
            self.drillCycleZValue = 0

        def Copy0to1(self):
            self.bank1X = self.bank0X
            self.bank1Y = self.bank0Y
            self.bank1Z = self.bank0Z
    
        def Copy1to0(self):
            self.bank0X = self.bank1X
            self.bank0Y = self.bank1Y
            self.bank0Z = self.bank1Z
    
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A class that can read a GCode file
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS GCodeMachine
    class GCodeMachine:

        STACKFRAME_POP_FP = 1

        OCODE_START_OF_LINE = 1
        OCODE_END_OF_LINE = 2

        #COVERAGE_CLASS GCodeMachine
        def __init__(self):
            self.FUNC_EXPR = "(ABS|ACOS|ASIN|COS|EXP|FIX|FUP|LN|ROUND|SIN|SQRT|TAN)"
            self.BINOP_EXPR = "^(MOD|AND|XOR|OR|\*\*|\*|\/|\+|\-)"
            self.REAL_EXPR = "([+-]?(\d+\.\d+|\.\d+|\d+\.|\d+))"
            self.ATAN_EXPR = "^(ATAN)\["
            #O100 OR O[#101+2] 
            self.O_EXPR = "^O(\d+|\[.+\])"
            self.O_OP_EXPR = "^(WHILE|IF|ELSE|ENDIF|ENDWHILE|SUB|ENDSUB|CALL|DO)"
            self.REAL_EXPR = "([+-]?(\d+\.\d+|\.\d+|\d+\.|\d+))"
            self.GREAL_EXPR = "^(G" + "(\d+\.\d+|\.\d+|\d+\.|\d+)" + ")"
            self.INT_EXPR = "\d+"
            self.AtoZ_SET_EXPR = "[ABCFIJKPQRXYZ]"
            self.AtoZ_REAL_EXPR = "^(" + self.AtoZ_SET_EXPR + self.REAL_EXPR + ")"

            self.ordinaryUnaryComboProg = re.compile("^" + self.FUNC_EXPR + "\[")
            self.binopProg = re.compile("^" + self.BINOP_EXPR)
            self.realNumberProg = re.compile("^" + self.REAL_EXPR)
            self.arcTangentComboProg = re.compile(self.ATAN_EXPR)
            self.NAME_EXPR = "<.+?>"
            self.PARAM_NUM_NAME_EXPR = "#(" + self.INT_EXPR + "|" + self.NAME_EXPR + ")"
            self.AtoZ_PARAM_EXPR = "^(" + self.AtoZ_SET_EXPR + self.PARAM_NUM_NAME_EXPR + ")"
            self.T_EXPR = "^(T(" + self.INT_EXPR + "|" + self.PARAM_NUM_NAME_EXPR + "))"
            self.S_EXPR = "^(S(" + self.REAL_EXPR + "|" + self.PARAM_NUM_NAME_EXPR + "))"
            self.H_EXPR = "^(H" + self.INT_EXPR + ")"

            self.O_Prog = re.compile(self.O_EXPR)
            self.O_OP_Prog = re.compile(self.O_OP_EXPR)
            self.GREAL_Prog = re.compile(self.GREAL_EXPR)
            self.GMN_Prog = re.compile("^([GMN]" + self.INT_EXPR + ")")
            self.ABCFIJKPQRXYZ_Prog = re.compile(self.AtoZ_REAL_EXPR)
            self.ABCFIJKPQRXYZ_Param_Prog = re.compile(self.AtoZ_PARAM_EXPR)
            self.AtoZ_EXPR_EXPR = "^(" + self.AtoZ_SET_EXPR + "\[)"
            self.ABCFIJKPQRXYZ_Expr_Prog = re.compile(self.AtoZ_EXPR_EXPR)
            self.T_Prog = re.compile(self.T_EXPR)
            self.S_Prog = re.compile(self.S_EXPR)
            self.H_Prog = re.compile(self.H_EXPR)

            self.FunctionSetABS = ["ABS", "ACOS", "ASIN", "COS", "EXP", "FIX", "FUP", "LN", "ROUND", "SIN", "SQRT", "TAN"]
            self.FunctionSetATAN = ["ATAN"]
            self.StartOfRealNumber = "+-.0123456789"
            self.machine = Blender4CNC.TheMachine()
            self.ggroups = [ ["G0", "G1", "G2", "G3", "G38.2", "G80", "G81", "G82", "G83", "G84", "G85", "G86", "G87", "G88", "G89"] ]
            self.ggroups.append(["G17", "G18", "G19"])
            self.ggroups.append(["G90", "G91"])
            self.ggroups.append(["G93", "G94"])
            self.ggroups.append(["G20", "G21"])
            self.ggroups.append(["G40", "G41", "G42"])
            self.ggroups.append(["G43", "G49"])
            self.ggroups.append(["G98", "G99"])
            self.ggroups.append(["G54", "G55", "G56", "G57", "G58", "G59", "G59.1", "G59.2", "G59.3"])
            self.ggroups.append(["G61", "G61.1", "G64"])
            self.mgroups = [ ["M0", "M1", "M2", "M30", "M60"], ["M3", "M4", "M5"], ["M7", "M9"], ["M8", "M9"], ["M48", "M49"] ]
            self.output = []

        #**********************************************************
        def go(self, filename):
            filename2 = filename
            self.oLocations = {}
            self.GetOLocations(filename2)
            self.goSub(filename2)
        #**********************************************************
        #**********************************************************
        def goSub(self, filename):
            #print("top of goSub")
            #print("oLocations=", self.oLocations)
            self.stack = []
            sf = [0, 0, copy.copy(self.machine.Parameters30), copy.copy(self.machine.LocalNamedParameters), "START", ""]
            self.stack.append(sf)
            origLine = ""
            try:
    #        if True:
                self.output = []
                machine = self.machine
                file1A = open(filename, 'r') 
                file1 = mmap.mmap(file1A.fileno(), length=0, access=mmap.ACCESS_READ)
                self.machine = machine
                outputLine = 1
                firstLine = True
                totalCount = 0
                while True: 
                    totalCount += 1
    #                if totalCount > 20:
    #                    X

                    (line, origLine, startLineFilePointer, endLineFilePointer) = self.GetNextLineFromGCodeFile(file1)
                    if line == None:            # End of file
                        break
                    if len(line) == 0:      # Skip blank lines   
                        continue;

                    # The line has had any comments removed
                    # It can consist of multiple segments (can be empty)
                    # Each segment may be a parameter setting, or a mid-line word
                    # Parameters start with "#", and mid-line words with a-d,f-m,p-t,x-z

                    # Parse a line into rs274 defined words (G0, #2=1, ... etc.)
                    words = self.parse(line)

                    # Check for line number
                    (lineNumWord, words) = self.CheckLineNumber(words)

                    # LinuxCNC defines 'O' subroutines with looping and branches
                    if self.HasOCode(words):
                        #print("goSub - handling O Code")
                        self.goHandleOCode(words, file1, startLineFilePointer, endLineFilePointer)
                        continue

                    # Remove any leading zeros from G and M codes
                    words = self.RemoveLeadingZerosGM(words)

                    if self.CountGMCodes(words) > 1:
                        self.CheckModalGCodes(words) # Check Modal G Codes
                        self.CheckModalMCodes(words) # Check Modal M Codes

                    # Verify that all other codes only appear once
                    for ch in "ABCDFHIJKLNOPQRSTXYZ":
                        self.VerifyCodesDoNotRepeat(words, ch)
                    
                    # For simulating the path there are a lot of codes we can ignore
                    words = self.IgnoreCertainCodeWords(words)

                    if len(words) == 0: # Skip if nothing left to do
                        continue

                    #print("goSub (2) line=", line)

                    # We should only really be left with G0-G3 codes
                    # OR G20, G21 (units = inches or mm)

                    # Now we run the simulated machine!

                    # Look for units G20 or G21
                    words = self.goHandle_G20_G21(words)
                    if len(words) == 0: # Skip if nothing left to do
                        continue

                    machine.Copy0to1()
                    self.goHandle_G81_DrillCycle(words)
                    self.goHandle_G73_G83_DrillCycle(words, "G73")
                    self.goHandle_G73_G83_DrillCycle(words, "G83")
                
                    # End a drill cycle
                    if "G80" in words:
                        machine.mode1 = "G0" # End of canned cycle goes back to G0 mode

                    # Do we have a G0, G1, G2 or G3 ?
                    for gcode in ["G0", "G1", "G2", "G3"]:
                        if gcode in words:
                            machine.mode1 = gcode

                    if machine.mode1 in ["G81", "G73", "G83"]:
                        self.goHandle_Mode_DrillCycle(words)

                    # Rapid/Feed
                    if machine.mode1 in ["G0", "G1"]:
                        self.goHandle_Mode_Move(words)

                    # Arc CW/CCW
                    if machine.mode1 in ["G2", "G3"]:
                        self.goHandle_Mode_Arc(words)

                    # Parameters
                    self.goHandle_Parameters(words)

                    machine.Copy1to0()
                    outputLine += 1
                    #print("goSub - end of while")
    #                machine.PrintPosition()
                    
            except Exception as err:
                error = "ERROR: "
                for e in err.args:
                    error += str(e) + " "
                error += " - " + origLine
                raise Exception(error)
                
            file1.close()
            file1A.close()
            
        #**********************************************************
        #
        #**********************************************************
        def goGetTokens(self, words):
            d = {}
            for k in "XYZIJRQ":  
                d[k] = None
            for word in words:
                if word[0] in "XYZIJRQ":  
                    word2 = self.readRealValue(word[1:])
                    d[word[0]] = self.EvaluateRealValue(word2)
            return d
        #**********************************************************
        #
        #**********************************************************
        def goTokensToVariables(self, d):
            return tuple([d[k] for k in "XYZIJRQ"])
        #**********************************************************
        # Parameters are all set in parallel which means we
        # have to copy all the parameters in case setting new
        # parameters refer to any other parameters that also
        # may be changing on this line
        #**********************************************************
        def goHandle_Parameters(self, words):
            # Check if we have any parameters at all
            haveParameters = False
            for word in words:
                if word[0] == "#": # We have a parameter being set
                    haveParameters = True
                    break
            if not haveParameters:                
                return
            
            self.newParam30 = copy.copy(self.stack[-1][2])
            self.newGlobalParameters = copy.copy(self.machine.GlobalParameters)
            self.newNamedLocalParameters = copy.copy(self.stack[-1][3])
            
            for word in words:
                value = None
                if word[0] == "#": # We have a parameter being set
                    if word[1] == "#": # We have an indirect parameter
                        (param, value) = self.EvaluateWordParameter(word)
                        indirect = self.GetParameter(param[2:])
#                        param = self.machine.Parameters[param]
                    else:
                        (param, value) = self.EvaluateWordParameter(word)
                        #print("EvaluateWordParameter (param, value)=", (param, value))

                    if param[0] == "#":
                        param = param[1:]
                    if param[0] == "<":
                        param = param[1:-1]
                    
                    # This could be an indirect parameter like ##3, at this point the 'param' variable will be set to #3
                    if param[0] == "#":
                        newParam = self.GetParameter(param[1:])
                        if int(newParam) != newParam:
                            raise Exception("Invalid - indirect parameter is not an integer")
                        param = str(int(newParam))
                            
                    self.SetParameter(param, value)

            self.stack[-1][2] = self.newParam30   
            self.stack[-1][3] = self.newNamedLocalParameters 
            self.machine.GlobalParameters = self.newGlobalParameters                   

        #**********************************************************
        #
        #**********************************************************
        def goHandle_Mode_Arc(self, words):
            # The following applies to when in the X-Y plane
            # If in mode G2 or G3, look for X and/or Y and/or Z and R (for radius format must have at
            # least one of X,Y,Z and must have R)
            # OR
            # look for at least one of X,Y and at least one of I,J
            # if there is a Z, then this is a helical arc
            d = self.goGetTokens(words)
            (x, y, z, i, j, r, q) = self.goTokensToVariables(d)

            if (x != None) or (y != None) or (z != None) or (i != None) or (j != None) or (r != None):
                if ((r != None) and ((i != None) or (j != None))):
                    raise Exception("Invalid Arc (R and I,J specified)")
                if (not (x != None) and not (y != None)):
                    if (r != None):
                        raise Exception("Invalid Arc (none of X,Y specified)")
                if (not (i != None) and not (j != None) and not (r != None)):
                    raise Exception("Invalid Arc (none of I,J,R specified)")
                if not (y != None):
                    y = self.machine.bank1Y
                if not (x != None):
                    x = self.machine.bank1X
                if r != None:
                    # We have radius format
                    (xCenter, yCenter) = self.GetCenterOfArcRadiusFormat(x, y, r)
                else:
                    # We have center format
                    if not (i != None):
                        i = 0.0
                    if not (j != None):
                        j = 0.0
                    # The i,j values are relative to current position?
                    xCenter = self.machine.bank0X + i
                    yCenter = self.machine.bank0Y + j
                    r = math.sqrt((x-xCenter)**2 + (y-yCenter)**2)

                self.machine.bank1X = x
                self.machine.bank1Y = y

                if self.machine.mode1 == "G2":
                    cw = -1
                else:
                    cw = 1
                self.output.append(("ARC_FEED", self.machine.bank1X, self.machine.bank1Y, xCenter, yCenter, cw))
        #**********************************************************
        #
        #**********************************************************
        def goHandle_Mode_Move(self, words):
            d = self.goGetTokens(words)
            (x, y, z, i, j, r, q) = self.goTokensToVariables(d)
            #print("goHandle_Mode_Move x=", x)
            if x != None:
                self.machine.bank1X = x
            if y != None:
                self.machine.bank1Y = y
            if z != None:
                self.machine.bank1Z = z
            if (x != None) or (y != None) or (z != None):
                if self.machine.mode1 == "G0":
                    s = "STRAIGHT_TRAVERSE"
                else:
                    s = "STRAIGHT_FEED"
                self.output.append((s, self.machine.bank1X, self.machine.bank1Y, self.machine.bank1Z))
        #**********************************************************
        #
        #**********************************************************
        def goHandle_Mode_DrillCycle(self, words):
            d = self.goGetTokens(words)
            (x, y, z, i, j, r, q) = self.goTokensToVariables(d)
            if x != None:
                self.machine.bank1X = x
            if y != None:
                self.machine.bank1Y = y
            if (x != None) or (y != None):
                # Move to next drill position
                self.output.append(("STRAIGHT_TRAVERSE", self.machine.bank1X, self.machine.bank1Y, self.machine.bank1Z))
                # Add in drill movement
                self.output.append(("STRAIGHT_FEED", self.machine.bank1X, self.machine.bank1Y, self.drillCycleZValue))
                self.output.append(("STRAIGHT_TRAVERSE", self.machine.bank1X, self.machine.bank1Y, self.drillCycleRValue))
        #**********************************************************
        #
        #**********************************************************
        def goHandle_G73_G83_DrillCycle(self, words, g73g83):
            # A peck drill cycle, look for R,Z,Q on the first line
            if (g73g83 in words):
                d = self.goGetTokens(words)
                (x, y, z, i, j, r, q) = self.goTokensToVariables(d)
                if not (r != None):
                    raise Exception("R not specified for " + g73g83 + " drill cycle")
                if not (z != None):
                    raise Exception("Z not specified for " + g73g83 + " drill cycle")
                if not (q != None):
                    raise Exception("Q not specified for " + g73g83 + " drill cycle")
                self.drillCycleRValue = r
                self.drillCycleZValue = z
                self.drillCycleQValue = q
                
                # Add in drill movement for where we currently are
                self.output.append(("STRAIGHT_FEED", self.machine.bank1X, self.machine.bank1Y, self.drillCycleZValue))
                self.output.append(("STRAIGHT_TRAVERSE", self.machine.bank1X, self.machine.bank1Y, self.drillCycleRValue))
                
                self.machine.mode1 = g73g83
        #**********************************************************
        #
        #**********************************************************
        def goHandle_G81_DrillCycle(self, words):
            # A drill cycle, look for R,Z on the first line
            if "G81" in words:
                d = self.goGetTokens(words)
                (x, y, z, i, j, r, q) = self.goTokensToVariables(d)
                if not (r != None):
                    raise Exception("R not specified for G81 drill cycle")
                if not (z != None):
                    raise Exception("Z not specified for G81 drill cycle")
                self.drillCycleRValue = r
                self.drillCycleZValue = z
                
                # Add in drill movement for where we currently are
                self.output.append(("STRAIGHT_FEED", self.machine.bank1X, self.machine.bank1Y, self.drillCycleZValue))
                self.output.append(("STRAIGHT_TRAVERSE", self.machine.bank1X, self.machine.bank1Y, self.drillCycleRValue))
                
                self.machine.mode1 = "G81"
        #**********************************************************
        #
        #**********************************************************
        def goHandle_G20_G21(self, words):
            words2 = []
            for gcode in words:
                if (gcode == "G20") and (self.machine.units == "METRIC"):
                    raise Exception("Changing units Imperial/Metric detected.")
                elif (gcode == "G21") and (self.machine.units == "IMPERIAL"):
                    raise Exception("Changing units Imperial/Metric detected.")
                elif (gcode == "G20") and (self.machine.units == None):
                    self.machine.units = "IMPERIAL"
                elif (gcode == "G21") and (self.machine.units == None):
                    self.machine.units = "METRIC"
                else:
                    words2.append(gcode)
            return words2
        #**********************************************************
        #
        #**********************************************************
        def goHandleOCode(self, words, file1, startLineFilePointer, endLineFilePointer):
            (oWord, oCmd, oExpression) = self.ProcessSubroutine(words)
            #print("goHandleOCode (oWord, oCmd, oExpression)=", (oWord, oCmd, oExpression))
            if oCmd in ["WHILE"]:
                result = self.EvaluateOExpression(oExpression)
                # Check if this is the start of while...endwhile or the end of do...while
                key = oWord + "ENDWHILE"
                #print("key=", key)
                haveDo = (key not in self.oLocations.keys())
                #print("haveDo=", haveDo)
                if not haveDo:
                    # Processing a while...endwhile
                    if result == 0: # Expression evaluated to false, so skip the while loop
                        file1.seek(self.oLocations[oWord + "ENDWHILE"][self.OCODE_END_OF_LINE])
                else:
                    # Processing a do...while
                    if result == 1: # Expression evaluated to true, so skip go back up to the do
                        file1.seek(self.oLocations[oWord + "DO"][self.OCODE_END_OF_LINE])
            elif oCmd in ["ENDWHILE"]:
                file1.seek(self.oLocations[oWord + "WHILE"][self.OCODE_START_OF_LINE])
            elif oCmd in ["IF"]:
                result = self.EvaluateOExpression(oExpression)
                if result == 0: # Expression evaluated to false, so skip down and implement the else
                    file1.seek(self.oLocations[oWord + "ELSE"][self.OCODE_END_OF_LINE])
            elif oCmd in ["ELSE"]:
                file1.seek(self.oLocations[oWord + "ENDIF"][self.OCODE_END_OF_LINE])
            elif oCmd in ["ENDIF"]:
                pass
            elif oCmd in ["SUB"]: # Skip to end of sub
                file1.seek(self.oLocations[oWord + "ENDSUB"][self.OCODE_END_OF_LINE])
            elif oCmd in ["CALL"]: 
                # A call statement may have 0 or more (up to 30) parameters on the line
                #listParams = self.GetCallParameters(oExpression)
                listParams = self.EvaluateListOfExpressions(oExpression)
                # Push the stack - with a return of end of this line
                # params30 is [2], local named parameters is [3]
                self.stack.append([startLineFilePointer, endLineFilePointer, copy.copy(self.stack[-1][2]), copy.copy(self.stack[-1][3]), oWord, oCmd])
                    
                # WATCH OUT FOR PARAMETERS BEING SET IN PARALLEL                    
                self.newParam30 = copy.copy(self.stack[-1][2])
                for i in range(0,len(listParams)):
                    self.SetParameter(str(i+1), listParams[i])
                self.stack[-1][2] = self.newParam30                    

                file1.seek(self.oLocations[oWord + "SUB"][self.OCODE_END_OF_LINE])
            elif oCmd in ["ENDSUB"]: 
                sf = self.stack.pop()
                file1.seek(sf[self.STACKFRAME_POP_FP])
            elif oCmd in ["DO"]:
                pass
            else:
                raise Exception("UNKNOWN_oCmd")
        #**********************************************************
        # 
        #**********************************************************
        def GetNextLineFromGCodeFile(self, file1):
            startLineFilePointer = file1.tell()
            line = file1.readline() # Get next line
            endLineFilePointer = file1.tell()
            if type(line) == bytes:
                line = line.decode()
            if not line:            # End of file
                return (None, "", -1, -1)
            line = line.strip()     # Strip white space
            origLine = copy.copy(line)

            # The first non-blank line can be demarcated by a '%'
            if startLineFilePointer == 0:
                if line == "%":
                    line = ""
            # Any other line with a '%' is the end of the program
            else:
                if line == "%":
                    return (None, "", -1, -1)

            if len(line) > 0:
                if line[0] == "/":      # Block deleted lines are skipped
                    line = ""
        
            line = line.upper()     # Uppercase
            line = self.RemoveComments(line)
            line = self.RemoveSemiColonComments(line)
            line = line.strip()     # Strip white space
            return (line, origLine, startLineFilePointer, endLineFilePointer)
        #**********************************************************
        # Build a dictionary of all the "O" subroutines in a GCode
        # file (if any)
        #**********************************************************
        def GetOLocations(self, filename):
            self.oLocations = {}
            file1 = None
            try:
                file1 = open(filename, 'r') 
                self.GetOLocationsSub(file1)
                file1.close()
            except Exception as err:
                if file1:
                    file1.close()
                raise err
        #**********************************************************
        def GetOLocationsSub(self, file1):
            while True: 
                (line, origLine, startLineFilePointer, endLineFilePointer) = self.GetNextLineFromGCodeFile(file1)
                if line == None:            # End of file
                    break
                if len(line) == 0:      # Skip blank lines   
                    continue;

                # Parse a line into rs274 defined words (G0, #2=1, ... etc.)
                words = self.parse(line)
                if self.HasOCode(words):
                    (oWord, oCmd, oExpression) = self.ProcessSubroutine(words)
                    if oCmd != "CALL":
                        self.oLocations[oWord + oCmd] = (oCmd, startLineFilePointer, endLineFilePointer)

        #********************************************************************************************
        # Check for comments inside comments
        #********************************************************************************************
        def RemoveComments(self, line):
            if "(" in line:
                self.CheckForRecursiveComments(line)

                # Remove any comments
                # Substitute from ( to ) containing any characters but the ? means be NON-greedy about it
                # eg. (comment) G1 (comment2)
                line = re.sub("\(.*?\)", "", line)
                line = line.strip()
            return line

        #********************************************************************************************
        # LinuxCNC talks about comments can start with ; and go to the end of the line
        # ALTHOUGH, ; inside ( ) comments is NOT considered part of a comment
        # therefore, we will chop off anything on a line that is after a ;
        #********************************************************************************************
        def RemoveSemiColonComments(self, line):
            pos = line.find(";")
            if pos != -1:
                return line[0:pos]
            return line

        #********************************************************************************************
        #********************************************************************************************
        def CountGMCodes(self, words):
            l = [0 for word in words if word[0] in "GM"]
            return len(l)
#            gs = 0
#            ms = 0
#            for word in words:
#                if word[0] == "G":
#                    gs += 1
#                elif word[0] == "M":
#                    ms += 1
#            return gs + ms


        #********************************************************************************************
        #********************************************************************************************
        def EvaluateListOfExpressions(self, expressions):
            output = []
            for ex in expressions:
                output.append(self.EvaluateExpression(ex))
            return output

        #********************************************************************************************
        #********************************************************************************************
        def HasOCode(self, words):
            l = [1 for word in words if word[0] == "O"]
            return (len(l) > 0)

        #********************************************************************************************
        # A valid subroutine looks like:
        # O{Number}{Function}[{expression}]
        # or
        # O{Expression}{Function}[{expression}]
        #********************************************************************************************
        def ProcessSubroutine(self, words):
            # First check that this is a valid start to a subroutine
            word = words[0]

            # Check for O subroutine
            m = self.O_Prog.match(word)
            if m:
                oWord = m.group(0)
            else:
                raise Exception("Invalid Subroutine 'O' Code")

            # Linux4CNC allows O codes like:
            # o[#101+2] call
            # as well as
            # o100

            # The 2nd word MUST be if, while, do, repeat, sub
            oCommand = words[1]
            acceptableWords = ["WHILE", "IF", "ELSE", "ENDIF", "ENDWHILE", "SUB", "ENDSUB", "CALL", "DO"]                    
            if oCommand not in acceptableWords:
                raise Exception("Invalid Subroutine - missing valid command - " + ",".join(acceptableWords))
            
            # If 2nd word is "while", "if" then we must have an expression for the remainder of the line
            if len(words) > 2:
                oExpression = words[2]
            else:
                oExpression = ""
            if oCommand in ["WHILE", "IF"]:
                if len(oExpression) == 0:
                    raise Exception("Invalid Subroutine - missing expression after %s", oCommand)
                if oExpression[0] != "[":
                    raise Exception("Invalid Subroutine - missing '[' to start expression")
                if oExpression[-1] != "]":
                    raise Exception("Invalid Subroutine - missing ']' to end expression")
                if len(words) > 3:
                    raise Exception("Invalid Subroutine - extra text after expression")
            # If 2nd word is "call" we may have 0 or many expressions for the remainder of the line
            elif oCommand in ["CALL"]:
                oExpression = words[2:]
            elif oCommand in ["ELSE", "ENDIF", "ENDWHILE", "SUB", "ENDSUB", "DO"]:
                if len(oExpression) != 0:
                    raise Exception("Invalid Subroutine - extra text after %s", oCommand)
            return (oWord, oCommand, oExpression)
            

        #********************************************************************************************
        #********************************************************************************************
        def GetCenterOfArcRadiusFormat(self, xValue, yValue, rValue):
            # We have radius format
            if (xValue == self.machine.bank0X) and (yValue == self.machine.bank0Y):
                raise Exception("Invalid Arc (end point cannot equal start point in radius format)")
            # Calculate the center point 
            x1 = self.machine.bank0X
            y1 = self.machine.bank0Y
            x2 = xValue
            y2 = yValue
            # Distance from start point to end point
            q = math.sqrt((x2-x1)**2 + (y2-y1)**2)

            # The RS274NGC spec. considers the radius to start and end points to be acceptable if it is 
            # within 0.0001
            prec = 5
            q = round(q, prec)
            q_2 = q/2
            q_2 = round(q_2, prec)
            rValue = round(rValue, prec)
            difference = abs(rValue - q_2)
           
            if (difference >= 0.000051) and (abs(rValue) < q_2):
                raise Exception("Invalid Arc (radius too small) rValue=%f, q_2=%f" % (rValue, q_2))
            # Halfway point between start end end points
            x3 = (x1 + x2) / 2
            y3 = (y1 + y2) / 2
            # Line from start to end is (x2-x1, y2-y1)
            xLine = (x2-x1)
            yLine = (y2-y1)
            # Vector of line (divide by q to normalize)
            xVec = xLine / q
            yVec = yLine / q
            # When radius is negative, choose longer arc, else choose shorter arc
            # For G2 and positive radius -> mirror line = (y, -x)
            # For G2 and negative radius -> mirror line = (-y, x)
            # For G3 and positive radius -> mirror line = (-y, x)
            # For G3 and negative radius -> mirror line = (y, -x)
            xMirror = yVec
            yMirror = -xVec
            if (self.machine.mode1 == "G2") and (rValue < 0):
                xMirror = -yVec
                yMirror = xVec
            if (self.machine.mode1 == "G3") and (rValue > 0):
                xMirror = -yVec
                yMirror = xVec
               
            # Distance to go along mirror line is SQRT( R**2 - (q/2)**2 )
            if difference <= 0.000051:
                # We are dealing with a tiny curve where we have lost precision beyond 0.0001
                # We will split the difference
                dist = difference / 2
            else:                   
                dist = math.sqrt( rValue**2 - (q_2)**2 )
            xCenter = x3 + dist * xMirror
            yCenter = y3 + dist * yMirror
            return (xCenter, yCenter)

        #********************************************************************************************
        #********************************************************************************************
        def IgnoreCertainCodeWords(self, words):
            # Order of execution
            # 1. comment (includes message).
            # 2. set feed rate mode (G93, G94 — inverse time or per minute).
            words = self.RemoveCodes(words, ["G93", "G94"])
            # 3. set feed rate (F).
            # 4. set spindle speed (S).
            # 5. select tool (T).
            words = self.RemoveCodesStartWith(words, ["F", "S", "T"])
            # 6. change tool (M6).
            # 7. spindle on or off (M3, M4, M5).
            # 8. coolant on or off (M7, M8, M9).
            # 9. enable or disable overrides (M48, M49).
            # 10. dwell (G4).
            words = self.RemoveCodes(words, ["M6", "M3", "M4", "M5", "M7", "M8", "M9", "M48", "M49", "G4"])

            # 11. set active plane (G17, G18, G19).
            # This will be added later
            words = self.RemoveCodes(words, ["G17", "G18", "G19"])

            # 12. set length units (G20, G21).
            # 13. cutter radius compensation on or off (G40, G41, G42)
            # 14. cutter length compensation on or off (G43, G49)
            words = self.RemoveCodes(words, ["G40", "G41", "G42", "G43", "G49"])
            # 15. coordinate system selection (G54, G55, G56, G57, G58, G59, G59.1, G59.2, G59.3).
            words = self.RemoveCodes(words, ["G54", "G55", "G56", "G57", "G58", "G59", "G59.1", "G59.2", "G59.3"])
            # 16. set path control mode (G61, G61.1, G64)
            # 17. set distance mode (G90, G91).
            # 18. set retract mode (G98, G99).
            words = self.RemoveCodes(words, ["G61", "G61.1", "G64", "G90", "G91", "G98", "G99"])
            # 19. home (G28, G30) or
            # change coordinate system data (G10) or
            # set axis offsets (G92, G92.1, G92.2, G94).
            words = self.RemoveCodes(words, ["G28", "G30", "G10", "G92", "G92.1", "G92.2", "G94"])
            # 20. perform motion (G0 to G3, G80 to G89), as modified (possibly) by G53.
#            self.RemoveCodes(words, ["G80", "G81", "G82", "G83", "G84", "G85", "G85", "G86", "G87", "G88", "G89", "G53"])
            words = self.RemoveCodes(words, ["G82", "G84", "G85", "G85", "G86", "G87", "G88", "G89", "G53"])
            # 21. stop (M0, M1, M2, M30, M60).
            words = self.RemoveCodes(words, ["M0", "M1", "M2", "M30", "M60"])
            return words

        #********************************************************************************************
        # Words like "G01" are changed to "G1"
        #********************************************************************************************
        def RemoveLeadingZerosGM(self, words):
            for i in range(0,len(words)):
                word = words[i]
                if (word[0] in "GM") and (word[1] == "0"):
                    word2 = self.readRealNumber(word[1:])
                    value = int(word2)
                    words[i] = word[0] + str(value)
            return words

        #********************************************************************************************
        #********************************************************************************************
        def EvaluateWordParameter(self, l):
            word = self.readParameter(l)
            l = l[len(word):]
            param = word            
            l = l[1:] # Remove the "="
            value = self.EvaluateRealValue(l)
            if (value != None):
                return (param, value)
            else:
                raise Exception("Error evaluating parameter - Invalid Parameter")

        def EvaluateParameter(self, l):
            if l[0] == "#":
                l = l[1:]
            if l[0] == "<":
                l = l[1:-1]
            return self.GetParameter(l)

        def EvaluateATANFunction(self, l):
            l = l[4:]     # Remove ATAN
            expr1 = self.readExpression(l)
            l = l[len(expr1):]  # Remove 1st expression
            l = l[1:]           # Remove "/"
            expr2 = self.readExpression(l)
            value1 = self.EvaluateExpression(expr1)
            value2 = self.EvaluateExpression(expr2)
            DEG2RAD = math.pi / 180
            RAD2DEG = 1 / DEG2RAD
            return math.atan2(value1, value2) * RAD2DEG

        def EvaluateFunction(self, l):
            m = self.ordinaryUnaryComboProg.match(l)
            if not m:
                raise Exception("Invalid Function?")
            word = m.group(1)
            l = l[len(word):]
            expr = self.readExpression(l)
            value = self.EvaluateExpression(expr)
            value = self.ApplyFunction(word, value)
            return value

        #********************************************************************************************
        # A "real" value in GCode may be the result of:
        # a) a float like 1.234
        # b) an expression like [24*0.5]
        # c) a parameter like #1 or #ABC
        # d) a function like ATAN, EXP...etc
        #********************************************************************************************
        def EvaluateRealValue(self, l):
            if l[0] in self.StartOfRealNumber:
                return float(l)
            elif l[0] == "[":
                return self.EvaluateExpression(l)
            elif (len(l) >= 2) and (l[0:2] == "##"):
                # We have an indirect parameter
                tempParam = self.EvaluateParameter(l[1:])
                if int(tempParam) != tempParam:
                    raise Exception("Invalid - indirect parameter is not an integer.")
                newParam = "#" + str(int(tempParam))
                return self.EvaluateParameter(newParam)
            elif l[0] == "#":
                return self.EvaluateParameter(l)
            elif (len(l) >= 4) and (l[0:4] == "ATAN"):
                return self.EvaluateATANFunction(l)
            else:
                return self.EvaluateFunction(l)

        #********************************************************************************************
        # Read a real value
        #********************************************************************************************
        def readRealValue(self, l):
            word = self.readRealNumber(l)
            if word is not None:
                return word

            word = self.readExpression(l)
            if word is not None:
                return word

            word = self.readParameter(l)
            if word is not None:
                return word

            word = self.readUnaryCombo(l)
            if word is not None:
                return word
            
            return None

        #********************************************************************************************
        # Get a "#" parameter that has been previously set, if not set, return 0.0
        # The parameter could be a numbered parameter, a local named parameter, or a global
        # parameter.
        #********************************************************************************************
        def GetParameter(self, ndx):
            #Parameters30 is number 2 in the tuple
            if ndx in self.stack[-1][2].keys():
                return self.stack[-1][2][ndx]
            #LocalNamedParameters is number 3 in the tuple
            elif ndx[0] not in "0123456789":
                return self.stack[-1][3][ndx]
            else:
                if ndx in self.machine.GlobalParameters.keys():
                    return self.machine.GlobalParameters[ndx]
                else:
                    return 0.0
                
        #********************************************************************************************
        # Set a parameter to a value
        # If the ndx is 0-30, set one of the special set of 30 register parameters
        # else set a global numbered parameter or a local named parameter
        #********************************************************************************************
        def SetParameter(self, ndx, value):
            try:
                val = int(ndx)
            except:
                val = 31
            param30 = (val <= 30)
            
            #Parameters30 is number 2 in the tuple
            #LocalNamedParameters is number 3 in the tuple
            if param30:
                self.newParam30[ndx] = value
            else:
                if ndx[0] in "0123456789":
                    self.newGlobalParameters[ndx] = value
                else:
                    self.newNamedLocalParameters[ndx] = value

        #********************************************************************************************
        # An O Expression is:
        #   [ {expression} EQ/LT/GT {expression} ]
        # This will evaluate the expression and return 1 for True, 0 for False
        #********************************************************************************************
        def EvaluateOExpression(self, l):
            if l[0] != "[":
                raise Exception("Invalid O Expression - missing '['")
            
            l = l[1:-1] # Remove leading and trailing [,]
            word = ""
            word = self.readRealValue(l)
            l = l[len(word):]
            value = self.EvaluateRealValue(word)

            if len(l) < 2:
                raise Exception("Invalid O Expression - missing EQ/LT/GT/LE/GE")
        
            op = l[0:2]
            l = l[2:]
            acceptableWords = ["EQ", "LT", "GT", "GE", "LE"]
            if op not in acceptableWords:
                raise Exception("Invalid O Expression %s" % ",".join(acceptableWords))

            word = self.readRealValue(l)
            l = l[len(word):]
            value2 = self.EvaluateRealValue(word)

            if op == "EQ":
                answer = value == value2
            elif op == "LT":
                answer = value < value2
            elif op == "LE":
                answer = value <= value2
            elif op == "GE":
                answer = value >= value2
            else: # op == "GT":
                answer = value > value2
                    
            if answer:
                return 1
            else:
                return 0
            
        #********************************************************************************************
        # A binary operator is something like: MOD AND XOR OR  **  * / + -
        #********************************************************************************************
        def readBinaryOperator(self, l):
            m = self.binopProg.match(l)
            if m:
                return m.group(1)
            return None

        #********************************************************************************************
        # These are general expressions NOT the more simplified "O" expressions
        #********************************************************************************************
        def EvaluateExpression(self, l):
            l = l[1:-1] # Remove leading and trailing "[", "]"

            # An expression can be a simple thing like [-10] or [+10] which will fall through safely as being 
            # just a real number but it could also be [-#1] or [+#1]
            # or [-[3*4]] or [+[3*4]]
            
            word = self.readRealValue(l)
            
            if word == None:
                if l[0] in "-+":
                    word = "0"
                else:
                    raise Exception("Invalid real value in Expression")
            else:
                l = l[len(word):]
            
            ops = [word]

            while len(l) != 0:
                word = self.readBinaryOperator(l)
                if word is None:
                    raise Exception("Invalid Binary Operator in expression")
                ops.append(word)
                l = l[len(word):]

                word = self.readRealValue(l)
                if word is None:
                    raise Exception("Invalid real value in Expression")
                ops.append(word)
                l = l[len(word):]

            # Apply the binary operators

            # First evaluate all the fields
            i = 0
            while i < len(ops):
                ops[i] = self.EvaluateRealValue(ops[i])
                i += 2

            # Now apply any power operators
            ops2 = [ops.pop(0)]
            while len(ops) > 0:
                op = ops.pop(0)
                if op == "**":
                    ops2[-1] = ops2[-1]**ops.pop(0)
                else:
                    ops2.append(op)
                    ops2.append(ops.pop(0))
            ops = ops2

            # Now apply any divide, modulo or times operators (left to right)
            ops2 = [ops.pop(0)]
            while len(ops) > 0:
                op = ops.pop(0)
                if op == "*":
                    ops2[-1] = ops2[-1]*ops.pop(0)
                elif op == "/":
                    ops2[-1] = ops2[-1]/ops.pop(0)
                elif op == "MOD":
                    ops2[-1] = ops2[-1] % ops.pop(0)
                else:
                    ops2.append(op)
                    ops2.append(ops.pop(0))
            ops = ops2

            # Lastly, apply any +,-,logical
            ops2 = [ops.pop(0)]
            while len(ops) > 0:
                op = ops.pop(0)
                if op in ["AND", "XOR", "OR"]:
                    a = ops2[-1]
                    b = ops.pop(0)
                    if op == "AND":
                        value = bool(a) and bool(b)
                    elif op == "XOR":
                        value = (bool(a) and not bool(b)) or (not bool(a) and bool(b))
                    else: # op == "OR":
                        value = bool(a) or bool(b)
                    if value == True:
                        ops2[-1] = 1 
                    else:
                        ops2[-1] = 0
                elif op == "+":
                    ops2[-1] = ops2[-1] + ops.pop(0)
                elif op == "-":
                    ops2[-1] = ops2[-1] - ops.pop(0)
            ops = ops2
            value = ops[0]

            # End while
            return value

        #********************************************************************************************
        # A binary operator is something like: MOD AND XOR OR  **  * / + -
        #********************************************************************************************
        def EvaluateBinaryOperator(self, l):
            if l[0] in "MAX": # could be modulo, and, xor
                if len(l) < 4:
                    raise Exception("Invalid binary operator")
            elif l[0] == "O": # could be or
                if len(l) < 3:
                    raise Exception("Invalid binary operator")
            elif l[0] == "*": # could be **
                if len(l) < 2:
                    raise Exception("Invalid binary operator")

            popextra = 0
            if l[0] == "*": # times or power
                if l[1] == "*": # power
                    binary_op = "power"
                    popextra = 1
                else:
                    binary_op = "times"
            elif l[0] == "/": # divide
                binary_op = "divide"
            elif (l[0] == "M") and ("".join(l[0:3]) == "MOD"):
                binary_op = "modulo"
                popextra = 2
            elif l[0] == "+": # plus
                binary_op = "plus"
            elif l[0] == "-": # minus
                binary_op = "minus"
            elif (l[0] == "A") and ("".join(l[0:3]) == "AND"):
                binary_op = "and"
                popextra = 2
            elif (l[0] == "X") and ("".join(l[0:3]) == "XOR"):
                binary_op = "xor"
                popextra = 2
            elif (l[0] == "O") and ("".join(l[0:2]) == "OR"):
                binary_op = "or"
                popextra = 1
            else:
                raise Exception("Invalid binary operator")
                
            l.pop(0)
            for i in range(0,popextra):
                l.pop(0)

            return binary_op

        #********************************************************************************************
        # The ATAN function is the only math function that has two inputs
        #********************************************************************************************
        def ApplyFunctionATAN(self, fn, value1, value2):
            DEG2RAD = math.pi / 180
            RAD2DEG = 1 / DEG2RAD
            if fn == "ATAN":
                return math.atan2(value1, value2) * RAD2DEG
            else:
                raise Exception("Invalid atan function")

        #********************************************************************************************
        # A function: ABS, ACOS, ASIN, COS, EXP, FIX, FUP, LN, ROUND, SIN, SQRT, TAN
        #********************************************************************************************
        def ApplyFunction(self, fn, value):
            DEG2RAD = math.pi / 180
            RAD2DEG = 1 / DEG2RAD
            prec = 13
            if fn == "ABS":
                value = abs(value)
            elif fn == "ACOS":
                value = math.acos(value) * RAD2DEG
            elif fn == "ASIN":
                value = math.asin(value) * RAD2DEG
            elif fn == "COS":
                value = math.cos(value * DEG2RAD)
            elif fn == "EXP":
                value = math.exp(value)
            elif fn == "FIX":
                value = math.floor(value)
            elif fn == "FUP":
                value = math.ceil(value)
            elif fn == "LN":
                value = math.log(value)
            elif fn == "ROUND":
                value = round(value)
            elif fn == "SIN":
                value = math.sin(value * DEG2RAD)
            elif fn == "SQRT":
                return math.sqrt(value)
            elif fn == "TAN":
                value = math.tan(value * DEG2RAD)
            else:
                raise Exception("Invalid function")
            return round(value, prec)
        
        #********************************************************************************************
        # Remove any unwanted codes
        # Remove any words that start with any letter in "codes"
        #********************************************************************************************
        def RemoveCodesStartWith(self, words, codes):
            words2 = []
            for word in words:
                if word[0] not in codes:
                    words2.append(word)
            return words2

        #********************************************************************************************
        # Remove any unwanted codes
        #********************************************************************************************
        def RemoveCodes(self, words, codes):
            for code in codes:
                while code in words:
                    words.remove(code)
            return words

        #********************************************************************************************
        # Check do not have two or more modal M codes on the same line
        #********************************************************************************************
        def CheckModalMCodes(self, words):
            # Verify no more than 4 M words on a line
            mList = [0 for word in words if word[0] == "M"]
#            count = 0
#            for word in words:
#                if word[0] == "M":
#                    count += 1
#            if count > 4:
            if len(mList) > 4:
                raise Exception("More than 4 modal 'M' commands on line")

            # Verify there are not 2 or more M commands from the same modal group (with exception of M7 and M8)
            # group 4 = {M0, M1, M2, M30, M60} stopping
            # group 6 = {M6} tool change
            # group 7 = {M3, M4, M5} spindle turning
            # group 8 = {M7, M8, M9} coolant (special case: M7 and M8 may be active at the same time)
            # group 9 = {M48, M49} enable/disable feed and speed override switches
            for grp in self.mgroups:
                self.VerifyModalMCodes(words, grp)

        #********************************************************************************************
        # Check do not have two or more modal G codes on the same line
        #********************************************************************************************
        def CheckModalGCodes(self, words):
            # Check that we do not have multiple G codes from the same modal group
            # The modal groups for G codes are:
            # group 1 = {G0, G1, G2, G3, G38.2, G80, G81, G82, G83, G84, G85, G86, G87, G88, G89} motion
            # group 2 = {G17, G18, G19} plane selection
            # group 3 = {G90, G91} distance mode
            # group 5 = {G93, G94} feed rate mode
            # group 6 = {G20, G21} units
            # group 7 = {G40, G41, G42} cutter radius compensation
            # group 8 = {G43, G49} tool length offset
            # group 10 = {G98, G99} return mode in canned cycles
            # group 12 = {G54, G55, G56, G57, G58, G59, G59.1, G59.2, G59.3} coordinate system selection
            # group 13 = {G61, G61.1, G64} path control mode
            for grp in self.ggroups:
                self.VerifyModalGCodes(words, grp)

        #********************************************************************************************
        # Check for valid line number (if any) 
        #********************************************************************************************
        def CheckLineNumber(self, words):
            if words[0][0] == "N":
                word = words.pop(0)
                set1 = set(word[1:])
                set2 = set("0123456789")
                if len(set1 - set2) > 0:
                    raise Exception("Invalid line number")
#                
#                for ch in word[1:]:
#                    if ch not in "0123456789":
#                        raise Exception("Invalid line number")
                if len(word) > 6:
                    raise Exception("Invalid line number (exceeds 5 digits)")
                return (word, words)
            return ("N.....", words)

        #********************************************************************************************
        # Comments inside comments are not allowed
        #********************************************************************************************
        def CheckForRecursiveComments(self, line):
            # Check for comments inside comments - this is NOT allowed
            # Do a non-greedy search
            result = re.findall("\(.*?\)", line)
            for s in result:
                result = re.match("\(.*\(", s)
                if result:
                    raise Exception("Invalid comment within comment")
       
        #********************************************************************************************
        # Check that a code like "x" or "A" only appears once on a line
        #********************************************************************************************
        def VerifyCodesDoNotRepeat(self, words, codes):
            for code in codes:
                l = [1 for word in words if word[0] == code]
                if len(l) > 1:
                    raise Exception("Code " + code + " appears multiple times on line")
#            found = False
#            for word in words:
#                if word[0] == code:
#                    if found:
#                        raise Exception("Code " + code + " appears multiple times on line")
#                    else:
#                        found = True

        #********************************************************************************************
        # Checks that a group of words do not contain two or more G codes from the same modal group
        #********************************************************************************************
        def VerifyModalGCodes(self, words, gcodes):
            l = [1 for word in words if word in gcodes]
            if len(l) > 1:
                raise Exception("Incompatible Codes (G or M) on line")
#            found = False
#            for word in words:
#                if word in gcodes:
#                    if found:
#                        raise Exception("Incompatible Codes (G or M) on line")
#                    else:
#                        found = True
        #********************************************************************************************
        # Checks that a group of words do not contain two or more M codes from the same modal group
        #********************************************************************************************
        def VerifyModalMCodes(self, words, gcodes):
            l = [1 for word in words if word in gcodes]
            if len(l) > 1:
                raise Exception("Incompatible Codes (G or M) on line")
#            found = False
#            for word in words:
#                if word in gcodes:
#                    if found:
#                        raise Exception("Incompatible Codes (G or M) on line")
#                    else:
#                        found = True

        #********************************************************************************************
        # Read +/-, then digits (and maybe a single decimal point) until we run out of digits
        # eg +123.456, -57, -.123, +0.0001
        #********************************************************************************************
        def readRealNumber(self, line):
            m = self.realNumberProg.match(line)
            if m:
                return m.group(1)
            return None
        
        #********************************************************************************************
        # Read [, then anything until a closing ]
        # Keep track of [ and matching to closing ]
        # e.g. [ 50 + 50 ], [50 + [10 + 10]]
        #********************************************************************************************
        def readExpression(self, line):
            if line[0] != "[":
                return None
            count = 1
            error = None
            len2copy = 1
            i = 1
            while i < len(line):
                if line[i] == "[":
                    count += 1
                elif line[i] == "]":
                    count -= 1
                len2copy += 1
                if count == 0:
                    break
                i += 1
            if count != 0:
                raise Exception("Invalid Expression")
            return line[:len2copy]

        #********************************************************************************************
        # Read #, then digits (maybe another starting #)
        # e.g. #10, ##2
        # LinuxCNC and a few other places seem to refer to named parameters
        # e.g. #<xscale>
        #********************************************************************************************
        def readParameter(self, line2):
            # Be non-greedy so we don't get all of #<a>=#<b> we just get #<a>
            self.parameterProg = re.compile("^(#(#\d+|\d+|<.+?>))")
            m = self.parameterProg.match(line2)
            if m:
                return m.group(1)

            # A parameter could be "#[...]"
            self.startExprProg = re.compile("^(#\[)")
            m = self.startExprProg.match(line2)
            if m:
                result = self.readExpression(line2[1:])
                if result is not None:
                    return "#" + result
            return None

        #********************************************************************************************
        # Read #, then digits then "=" then real number or another parameter
        # e.g. #2=7.0, #2=#3, #<XSCALE>=1.0
        #********************************************************************************************
        def readParameterWord(self, line):
            result = self.readParameter(line)
            if result is None:
                return None
            word = result
            line = line[len(result):]

            if line[0] != "=":
                return None
            word += line[0]
            line = line[1:]

            result = self.readRealValue(line)
            if result is not None:
                word += result
                return word
            return None

        #********************************************************************************************
        # read in a function name like abs or atan
        #********************************************************************************************
        def readUnaryCombo(self, line):
            word = self.readOrdinaryUnaryCombo(line)
            if word is not None:
                return word
            
            word = self.readArcTangentCombo(line)
            if word is not None:
                return word
            return None

        #********************************************************************************************
        # Read in a function name like abs (any function EXCEPT atan)
        #********************************************************************************************
        def readOrdinaryUnaryCombo(self, line):
            m = self.ordinaryUnaryComboProg.match(line)
            if m:
                word1 = m.group(1)
                line = line[m.end()-1:]
                word = self.readExpression(line)
                return word1 + word
            return None

        #********************************************************************************************
        # Read in atan function
        #********************************************************************************************
        def readArcTangentCombo(self, line):
            m = self.arcTangentComboProg.match(line)
            if m:
                word1 = m.group(1)
                line = line[m.end()-1:]
                word = self.readExpression(line)
                word1 += word
                line = line[len(word):]
                if line[0] != "/":
                    raise Exception("Invalid ATAN Function")
                word1 += "/"
                line = line[1:]
                word = self.readExpression(line)
                if word is None:
                    raise Exception("Invalid ATAN Function")
                return word1 + word
            return None

        #********************************************************************************************
        # Read in a "word" as defined by rs274
        #********************************************************************************************
        def readword(self, l):
            line2 = l

            # Check for G (eg. G38.2)
            m = self.GREAL_Prog.match(line2)
            if m:
                return m.group(1)

            # Check for G or M or N (eg. G20, N30, M04)
            m = self.GMN_Prog.match(line2)
            if m:
                return m.group(1)

            # Check for ABCFIJKPQRXYZ word (e.g. X+10.25)
            m = self.ABCFIJKPQRXYZ_Prog.match(line2)
            if m:
                return m.group(1)
            # Check for ABCFIJKPQRXYZ word with parameter (e.g. X#10, X#<scale>)
            m = self.ABCFIJKPQRXYZ_Param_Prog.match(line2)
            if m:
                return m.group(1)
            # Check for ABCFIJKPQRXYZ word with expression (e.g. X[#<scale>])
            m = self.ABCFIJKPQRXYZ_Expr_Prog.match(line2)
            if m:
                # We must correctly trace the expression and extract it
                word = self.readExpression(line2[1:])
                return line2[0] + word

            # Check for T word (e.g. T05 or T#<scale>)
            m = self.T_Prog.match(line2)
            if m:
                return m.group(1)

            # Check for S word (e.g. S10.25 or S#<scale>)
            m = self.S_Prog.match(line2)
            if m:
                return m.group(1)

            # Check for H word (e.g. H1)
            m = self.H_Prog.match(line2)
            if m:
                return m.group(1)

            # Check for O subroutine
            m = self.O_Prog.match(line2)
            if m:
                return m.group(0)

            # Check for O OP code
            m = self.O_OP_Prog.match(line2)
            if m:
                return m.group(0)

            # D? or L?

            result = self.readParameterWord(line2)
            if result is not None:
                return result

            result = self.readExpression(line2)
            if result is not None:
                return result

            result = self.readUnaryCombo(line2)
            if result is not None:
                return result
            
            raise Exception("Invalid Word")

        def parse(self, line):
            line = re.sub("\s", "", line) # Remove any whitespace
            l = line
            words = []
            while len(l) > 0:
                word = self.readword(l)
                l = l[len(word):]
                words.append(word)
            return words
#END_COVERAGE#


    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A class for handling Polytoxogons - verifying them, and adding and subtracting
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS Polytoxogon
    class Polytoxogon:

        #********************************************************************
        # Returns True if point is a line
        #********************************************************************
        def PointIsStraight(self, p):
            return len(p) == 2
                
        #********************************************************************
        # Returns True if line is a line
        #********************************************************************
        def SegmentIsStraight(p):
            return len(p[1]) == 2
                
        #********************************************************************
        #
        #********************************************************************
        def __init__(self, points):
            self.points = points            # The list of points defining the shape 
            if self.PointsRepresentCircle(points):
                # Split a circle into 2 semi-circles
                if len(points[0]) == 5:
                    self.points = [points[1], points[0]]
                mid = self.BreakUpCircle()
                self.points = [self.points[1], mid]
            self.lines = self.GetListOfLinesFromPoints(self.points)
            
            self.ambiguous = None
            self.polys = None
            self.overlapPolys = None
            
            # Set all debugging to False
            self.debug = {}
            method_list = [func for func in dir(self) if callable(getattr(self, func))]
            for fn in method_list:
                if fn[0] != '_':
                    methodName = self.__class__.__name__ + "." + fn
                    self.debug[methodName] = False

        #********************************************************************
        # Make it hashable so they can be in sets etc.
        #********************************************************************
        def __hash__(self):
            return id(self)

        #********************************************************************
        #
        #********************************************************************
        def __repr__(self):
            return self.__str__()
            
        #********************************************************************
        #
        #********************************************************************
        def __str__(self):
            maxLen = 0
            for pp in self.points:
                s = self.GetVectorAsString(pp)
                if len(s) > maxLen:
                    maxLen = len(s)
            maxLen += 6
            maxLen += 3

            ret = "\n"
            ret += "+" + "-" * (maxLen+1) + "+\n"

            for i in range(0,len(self.points)):
                pp = self.points[i]
                s = self.GetVectorAsString(pp)
                space = " " * (maxLen - len(s) - 2 - 3)
                ret += "| %3d " % i + s + space + " |\n"
            ret += "+" + "-" * (maxLen+1) + "+\n"
            ret += str(self.points) + "\n"
            return ret

        #********************************************************************
        # Check points are equal within tolerance
        #********************************************************************
        def __eq__(self, obj):
            if not isinstance(obj, Blender4CNC.Polytoxogon):
                return False
            if len(self.points) != len(obj.points):
                return False
            FEQ = Blender4CNC.FloatsAreEqual
            for i in range(0,len(self.points)):
                if len(self.points[i]) != len(obj.points[i]):
                    return False
                for j in range(0,len(self.points[i])):
                    if not FEQ(self.points[i][j], obj.points[i][j]):
                        return False
            return True

        #********************************************************************
        # Used at the top of each function for debugging purposes
        #********************************************************************
        def DEBUG_METHOD_HEADER(self, tf=False):
            if not tf:
                return (0,0,0)
            methodName = self.__class__.__name__ + "." + inspect.stack()[1][3]
            indent = None
            indent = " " * len(inspect.stack()) * 2
            self.debug[methodName] = tf
            if self.debug[methodName]:
                print(indent, methodName, "*" * 30)
            return (methodName, indent, self.debug[methodName])
        
        #********************************************************************
        # Print a dictionary nicely
        #********************************************************************
        def printPrettyDictionary(self, p, indent = "", title = ""):
            if indent == None:
                indent = ""

            maxLen = 60
            print(indent, "+", "-" * (maxLen+1), "+")
            s = title
            space = " " * (maxLen - len(s) - 2)
            print(indent, "| ", s, space, " |")            
            print(indent, "+", "-" * (maxLen+1), "+")

            for k in p.keys():
                print(indent, str(k), ": ", str(p[k]))

        #********************************************************************
        # Print a list of points nicely
        #********************************************************************
        def IndentStr(self, s, indent):
            lines = s.split("\n")
            lines2 = [indent + " " + x + "\n" for x in lines]
            lines = ""
            for line in lines2:
                lines += line
            return lines
        def printPrettyPoints(self, p, indent = "", title = ""):
            if indent == None:
                indent = ""
            maxLen = 0
            for pp in p:
                s = self.GetVectorAsString(pp)
                if len(s) > maxLen:
                    maxLen = len(s)
            maxLen += 6
            maxLen += 3

            print(indent, "+", "-" * (maxLen+1), "+")
            s = title
            space = " " * (maxLen - len(s) - 2)
            print(indent, "| ", s, space, " |")            

            for i in range(0,len(p)):
                pp = p[i]
                s = self.GetVectorAsString(pp)
                space = " " * (maxLen - len(s) - 2 - 3)
                print(indent, "| %3d" % i, s, space, " |")            

            print(indent, "+", "-" * (maxLen+1), "+")

        #********************************************************************
        # Print a list of lines nicely
        #********************************************************************
        def printPrettyLines(self, p, indent = "", title = ""):
            if indent == None:
                indent = ""
            if p == None:
                print(indent, "+------+")
                print(indent, "+ None +")
                print(indent, "+------+")
                return
            
            if indent == None:
                indent = ""
            maxLen = 0
            for pp in p:
                s = self.GetLineAsString(pp)
                if len(s) > maxLen:
                    maxLen = len(s)
            maxLen += 6
            maxLen += 3

            print(indent, "+", "-" * (maxLen+1), "+")
            s = title
            space = " " * (maxLen - len(s) - 2)
            print(indent, "| ", s, space, " |")            

            for i in range(0,len(p)):
                pp = p[i]
                s = self.GetLineAsString(pp)
                space = " " * (maxLen - len(s) - 2 - 3)
                print(indent, "| %3d" % i, s, space, " |")            

            print(indent, "+", "-" * (maxLen+1), "+")

        #********************************************************************
        # Print a list of lines - coordinates to copy into spreadsheet
        #********************************************************************
        def printPrettyLinesSS(self, p, indent = "", title = ""):
            if indent == None:
                indent = ""
            print(indent, "Printing Lines for Spreadsheet")
            print(indent, "X Coordinates")
            for i in range(0,len(p)):
                pp = p[i]
                print(str(pp[0][0]))
                print(str(pp[1][0]))
            print(indent, "Y Coordinates")
            for i in range(0,len(p)):
                pp = p[i]
                print(str(pp[0][1]))
                print(str(pp[1][1]))


#START_COVERAGE#
        #COVERAGE_CLASS Polytoxogon

        #********************************************************************
        # 
        #********************************************************************
        def ScalePoint(self, p, m):
            if len(p) != 2:
                return (p[0] * m, p[1] * m, p[2] * m, p[3] * m, p[4])
            else:
                return (p[0] * m, p[1] * m)
        def ScalePolyPoints(self, m):
            l = self.points
            for i in range(0,len(l)):
                l[i] = self.ScalePoint(l[i], m)
            l = self.lines
            for i in range(0,len(l)):
                line = l[i]
                p1 = self.ScalePoint(line[0], m)
                p2 = self.ScalePoint(line[1], m)
                l[i] = (p1, p2)
            return self

        #********************************************************************
        # Given a line and a list of sorted intersections along that line,
        # return a list of cut lines.
        # e.g. lineA = (0,0) to (0,10) and 
        #      sortedOverlapsA = [(0,2), (0,6)]
        #      returns (0,0) to (0,2) and
        #              (0,2) to (0,6) and
        #              (0,6) to (0,10) in a list
        #********************************************************************
        def SplitLineInfiniteOnInts(self, lineA, sortedOverlapsA):
            PEQ = self.PointsAreEqual
            (a1, a2) = lineA
            
            # sortedOverlapsA *CAN* have duplicates
            FEQ = Blender4CNC.FloatsAreEqual
            l = []
            changed = True
            while changed:
                changed = False
                for i in range(0,len(sortedOverlapsA)-1):
                    p = sortedOverlapsA[i]
                    q = sortedOverlapsA[i+1]
                    if not (FEQ(p[0], q[0]) and FEQ(p[1], q[1])):
                        l.append(p)
            l.append(sortedOverlapsA[-1])
            sortedOverlapsA = l
            
            if len(sortedOverlapsA) > 0:
                # If necessary, remove the start point
                (x,y) = a1[0:2]
                p = sortedOverlapsA[0]
                if FEQ(p[0], x) and FEQ(p[1], y):
                    sortedOverlapsA.pop(0)
            if len(sortedOverlapsA) > 0:
                # If necessary, remove the end point
                (x,y) = a2[0:2]
                p = sortedOverlapsA[-1]
                if FEQ(p[0], x) and FEQ(p[1], y):
                    sortedOverlapsA.pop(-1)
            
            if len(sortedOverlapsA) == 0:
                cutListA = [lineA]
            else:
                cutListA = self.CutLineOnIntersections(lineA, sortedOverlapsA)
            return cutListA
        #********************************************************************
        # Get a list of all lines that have infinite overlaps
        #********************************************************************
        def GetListOfLinesWithInfiniteOverlaps(self):
            # To save on iterating multiple times (potentially) over the whole list of lines in the poly
            # just get a short list of those lines that have an overlap
            lines = set([])
            for i,lineA in enumerate(self.lines):
                if lineA not in lines:
                    for j,lineB in enumerate(self.lines):
                        if i == j:
                            continue
                        ints = self.GetAllIntersections(lineA, lineB)
                        if ints == inf:
                            # We have two overlapping line segments
                            lines.add(lineA)
                            lines.add(lineB)
                            break
            return list(lines)
        #********************************************************************
        # Get a list of overlaps for each line (a line may overlap multiple lines)
        # and sort the list of intersections along the line
        # and cut the line at those points (if necessary)
        #********************************************************************
        def GetDictionaryOfCutLinesForOverlaps(self, lines):
            overlaps = {}
            # Get a list of overlaps for each line (a line may overlap multiple lines)
            # and sort the list of intersections along the line
            # and cut the line at those points (if necessary)
            for i,lineA in enumerate(lines):
                overlaps[lineA] = []
                for j,lineB in enumerate(lines):
                    if i == j:
                        continue
                    if self.GetAllIntersections(lineA, lineB) == inf:
                        overlaps[lineA] += self.GetOverlap(lineA, lineB)
                overlaps[lineA] = self.OrderIntersections(lineA, overlaps[lineA])
                if overlaps[lineA] == []:
                    cutListA = [lineA]
                else:
                    cutListA = self.SplitLineInfiniteOnInts(lineA, overlaps[lineA])
                overlaps[lineA] = cutListA
            return overlaps
        #********************************************************************
        # Return a list of infinite overlap stubs
        #********************************************************************
        def RemoveStubsAndGetListOfOverlapStubs(self, overlapLines, infiniteDepthCount = 0, infiniteDepthLimit = 30):
            if infiniteDepthCount >= infiniteDepthLimit:
                raise Blender4CNC.PolyException("RemoveStubsAndGetListOfOverlapStubs function exceeded depth recursion.", (self.points[0][0], self.points[0][1]))
            stubs = []
            usedLines = []
            for i in range(-1, len(self.lines)-1):
                lineA = self.lines[i]
                if lineA not in overlapLines:
                    continue
                lineB = self.lines[i+1]
                if self.GetAllIntersections(lineA, lineB) == inf:
                    usedLines.append(i)
                    usedLines.append(i+1)
                    stubs.append(Blender4CNC.Polytoxogon([lineA[1], lineB[1]]))
            if len(usedLines) == 0:
                return (copy.copy(self), [])
            usedLines = list(set(usedLines))
            usedLines.sort()
            if usedLines[0] == -1:
                usedLines.pop(0)
                usedLines.append(len(self.lines)-1)
            usedLines = list(set(usedLines))
            usedLines.sort()
            usedLines.reverse()
            #print("usedLines=", usedLines)
            #print("self.lines=", self.lines)
            for ndx in usedLines:
                self.lines.pop(ndx)
            points = [x[1] for x in self.lines]
            newPoly = Blender4CNC.Polytoxogon(points)
            # The new poly *CAN* have stubs (internal overlaps attached to stubs have now become stubs)
            (newPoly, stubs2) = newPoly.RemoveStubsAndGetListOfOverlapStubs(overlapLines, infiniteDepthCount+1)
            return (newPoly, stubs+stubs2)
        #********************************************************************
        # Find any lines that partially overlap and convert points/lines
        # so that we only have sgements with full overlaps
        #
        # EXAMPLE line ab partially overlaps line bc
        #         (This example produces a stub between c and b.)
        # a-----b   becomes  a--c==b
        # |  c--b            |  |
        # |  |               d--e
        # d--e
        #********************************************************************
        def RemovePartialOverlaps(self):
            lines = self.GetListOfLinesWithInfiniteOverlaps()
            # If there are no overlapping lines, just return self
            if len(lines) == 0:
                return self
            overlaps = self.GetDictionaryOfCutLinesForOverlaps(lines)
            # Now we have a dictionary that shows LineA -> line0, line1, line2....etc.
            # Now recreate the poly with any lines replaced by a cut list of multiple lines
            newLines = []
            for line in self.lines:
                if line not in overlaps.keys():
                    newLines.append(line)
                else:
                    newLines += overlaps[line]
            newPoints = [x[1] for x in newLines]
            newPoints = [newPoints[-1]] + newPoints[:-1]
            return Blender4CNC.Polytoxogon(newPoints)
        #********************************************************************
        # Given a poly with no stubs, will split on infinite overlaps and
        # return a list of simple polys
        #********************************************************************
        def SplitNoStubsPolyOnInfiniteOverlaps(self, overlapLines, totalOverlapLines, infiniteDepthCount = 0, infiniteDepthLimit = 30):
            if infiniteDepthCount >= infiniteDepthLimit:
                raise Blender4CNC.PolyException("SplitNoStubsPolyOnInfiniteOverlaps function exceeded depth recursion.", (self.points[0][0], self.points[0][1]))
            ndx = 0
            while ndx < len(self.lines):
                if self.lines[ndx] not in totalOverlapLines:
                     ndx += 1
                # THis code is not needed
                #elif self.lines[ndx] not in overlapLines:
                #     ndx += 1
                else:
                    lineA = self.lines[ndx]
                    ndxA = self.lines.index(lineA)
                    for ndxB,lineB in enumerate(overlapLines):
                        if lineA == lineB:
                            continue
                        if self.GetAllIntersections(lineA, lineB) == inf:
                            break
                    ndxB = self.lines.index(lineB)
                    # Everything prior gets made into polyA
                    points = self.lines[:ndxA] + self.lines[ndxB+1:]
                    points = [x[1] for x in points]
                    polyA = Blender4CNC.Polytoxogon(points)
                    # Everything after becomes polyB
                    points = self.lines[ndxA+1:ndxB]
                    points = [x[1] for x in points]
                    polyB = Blender4CNC.Polytoxogon(points)
                    # The overlap Poly
                    points = [self.lines[ndxA], self.lines[ndxB]]
                    points = [x[1] for x in points]
                    polyOverlap = Blender4CNC.Polytoxogon(points)
                    # Clean up the overlapLines list
                    ndxA = overlapLines.index(lineA)
                    overlapLines.pop(ndxA)
                    ndxB = overlapLines.index(lineB)
                    overlapLines.pop(ndxB)
                    # PolyA and polyB *MAY* contain stubs now
                    (polyA, stubsA) = polyA.RemoveStubsAndGetListOfOverlapStubs(totalOverlapLines)
                    (polyB, stubsB) = polyB.RemoveStubsAndGetListOfOverlapStubs(totalOverlapLines)
#                    if len(stubsA) != 0:
#                        X
#                    if len(stubsB) != 0:
#                            print(indent, self.IndentStr(str(polyA), indent))
#                            print(indent, self.IndentStr(str(polyB), indent))
#                            print(indent, stubsB)
#                        Y
                    # Split polyA and polyB if necessary
                    polysA = polyA.SplitNoStubsPolyOnInfiniteOverlaps(overlapLines, totalOverlapLines, infiniteDepthCount+1)
                    polysB = polyB.SplitNoStubsPolyOnInfiniteOverlaps(overlapLines, totalOverlapLines, infiniteDepthCount+1)
                    return polysA + [polyOverlap] + polysB + stubsA + stubsB
            # SHOULD NEVER GET HERE
            return [self]
        #********************************************************************
        # If a polytoxogon contains any overlapping lines, (while still
        # remaining clockwise and proper), this function will split the 
        # polytoxogon into multiple parts. It will split it into each region
        # that contains no overlaps, and each overlapping line segment will
        # be a separate part.
        # i.e. o--o==o--o -> o--o  o--o  o--o
        #      |  |  |  |    |  |        |  |
        #      o--o  o--o    o--o        o--o
        #      (1 poly becomes 3 polys)
        # Star shapes create a complexity!!!
        # Returns a list of polys.
        #********************************************************************
        def SplitPolyOnInfiniteOverlaps(self):

            newPoly = self.RemovePartialOverlaps()
            # The new poly will have overlapping line segments that are exactly paired with just one other segment
            # we can now split the poly more easily.
            
            # Just get a list of overlapping lines
            overlapLines = newPoly.GetListOfLinesWithInfiniteOverlaps()

            # Get a list of overlap stubs
            (newPoly, stubs) = newPoly.RemoveStubsAndGetListOfOverlapStubs(overlapLines)

            # At this point, stubs is a list of overlapping stubs, overlapLines is a list of non-stub overlaps
            totalOverlapLines = copy.copy(overlapLines)
            if len(newPoly.lines) == 0:
                polys = []
            elif len(overlapLines) == 0:
                polys = [newPoly]
            else:
                polys = newPoly.SplitNoStubsPolyOnInfiniteOverlaps(overlapLines, totalOverlapLines,  0)

            polys += stubs
            return polys

        #********************************************************************
        # The list of points represent a list of points along an open path
        # We repeat the points in the reverse direction so that we get a
        # closed poly (with zero area).
        # We return the new poly
        #********************************************************************
        def PolyFromPath(self, pointsIn, dist, infiniteLoopCounter = 1000):
            l = pointsIn
            FEQ = Blender4CNC.FloatsAreEqual

            # If there is just one point then this is just a hole
            if len(pointsIn) == 1:
                c = pointsIn[0]
                p1 = (c[0]+dist, c[1], c[0], c[1], 1)
                p2 = (c[0]-dist, c[1], c[0], c[1], 1)
                poly = Blender4CNC.Polytoxogon([p1, p2])
                return (poly, [])

            # If there are just two points and they are the same X,Y and the 2nd point is a curve, then this is a circle
            if len(pointsIn) == 2:
                if FEQ(pointsIn[0][0], pointsIn[1][0]) and FEQ(pointsIn[0][1], pointsIn[1][1]):
                    if len(pointsIn[1]) > 2:
                        # Circle!
                        points = [x for x in pointsIn]
                        poly = Blender4CNC.Polytoxogon(points)
                        if poly.points[0][4] == -1:
                            # Make sure the circle is defined to be clockwise (regardless of the actual path)
                            poly = poly.ReverseLineDirections()
                        newPoly = poly.Expand(None, dist)
                        # Ignore any tenons (well there won't be any)
                        newPoly = newPoly[0]
                            
                        r = self.GetArcRadius((newPoly.lines[0][0], newPoly.lines[0][1]))
                        if r > (dist*2):
                            tenonList = poly.Shrink(dist)
                            tenon = tenonList[0]
                            tenon = tenon.ReverseLineDirections()
                            tenons = [tenon]
                        else:
                            tenons = []
                        # Do not think it is possible for r <= dist!
                        #else:
                        # Start the main poly from a point close to the start of the path
                        mainPoly = newPoly
                        origStartPoint = pointsIn[0]
                        distances = [(x[0]-origStartPoint[0])**2+(x[1]-origStartPoint[1])**2 for x in mainPoly.points]
                        minDist = min(distances)
                        ndx = distances.index(minDist)
                        #print(origStartPoint, minDist, ndx, distances, mainPoly.points)
                        l = mainPoly.points[ndx:] + mainPoly.points[:ndx]
                        mainPoly = Blender4CNC.Polytoxogon(l)
                        return (mainPoly, tenons)
            # END circle

            if l[0] == l[-1]:
                l = l[0:-1]
                poly = Blender4CNC.Polytoxogon(l)
                poly2 = poly.ReverseLineDirections()
                points = [x[1] for x in poly.lines]
                points2 = [x[1] for x in poly2.lines]
                points += points2
            else:
                poly = Blender4CNC.Polytoxogon(l)
                poly2 = poly.ReverseLineDirections()
                points = [x[1] for x in poly.lines[0:-1]]
                points2 = [x[1] for x in poly2.lines[1:]]
                points = [points2[-1]] + points + points2[:-1]
            poly = Blender4CNC.Polytoxogon(points)
            
            # Clean up the poly
            poly.CleanUpPoly_UI()
            
            origPoly = copy.copy(poly)
            polyList = poly.ShrinkExpandAndSplit(dist, 1)
            
            # At this point, we have a list of polys 
            # Get the main largest poly
            rects = [poly.GetBoundingRectangle() for poly in polyList]
            areas = [(r[2]-r[0]) * (r[3]-r[1]) for r in rects]
            maxArea = max(areas)
            ndx = areas.index(maxArea)
            mainPoly = polyList[ndx]
            
            # Identify which polys touch the main poly
            polyList.remove(mainPoly)
            tenonsThatTouchMain = []
            tenonsThatDoNotTouchMain = []
            for poly in polyList:
                if poly.Overlap(mainPoly):
                    tenonsThatTouchMain.append(poly)
                else:
                    tenonsThatDoNotTouchMain.append(poly)
            # The invalid polys we have identified so far have to ALSO touch other tenons to be
            # truly invalid
            invalidPolyList = []
            for poly in tenonsThatTouchMain:
                for poly2 in tenonsThatDoNotTouchMain:
                    # The following is impossible
                    #if poly == poly2:
                    #    continue
                    if poly.Overlap(poly2):
                        invalidPolyList.append(poly)
                        break
            # Remove the invalid polys that touch the main poly
            totalInvalidPolyList = invalidPolyList
            for poly in invalidPolyList:
                polyList.remove(poly)
            # Identify which polys are "invalid" because they touch the original lines poly
            invalidPolyList = []
            for poly in polyList:
                if poly.Overlap(origPoly):
                    invalidPolyList.append(poly)
            # Remove the invalid polys that touch the original poly
            totalInvalidPolyList += invalidPolyList
            for poly in invalidPolyList:
                polyList.remove(poly)

            loopCount = 0
            while True:                
                loopCount += 1
                if loopCount > infiniteLoopCounter:
                    raise Blender4CNC.PolyException("Infinite loop in PolyFromPath", (pointsIn[0][0], pointsIn[0][1]))
                # It is still possible to have invalid polys that are bridging between tenons
                # In this situation, the "good" tenons only touch ONE other tenon AT MOST
                goodPolys = []
                for poly in polyList:
                    count = 0
                    for poly2 in polyList:
                        if poly == poly2:
                            continue
                        if poly.Overlap(poly2):
                            count += 1
                    if count <= 1:
                        goodPolys.append(poly)
                # If a poly touches a "good" poly and is not itself a "good" poly, then we want to remove
                # it from the list
                invalidPolys = []
                for poly in polyList:
                    if poly in goodPolys:
                        continue
                    # FAILS COVERAGE
                    for poly2 in goodPolys:
                        if poly == poly2:
                            continue
                        if poly.Overlap(poly2):
                            invalidPolys.append(poly)
                            break
                if len(invalidPolys) == 0:
                    break
                # FAILS COVERAGE
                totalInvalidPolyList += invalidPolyList
                for poly in invalidPolys:
                    polyList.remove(poly)
            # End while
            tenons = polyList            

            # Clean up the poly and tenons
            mainPoly.CleanUpPoly_UI()
            for tenon in tenons:
                tenon.CleanUpPoly_UI()

            # Make sure the main poly is clockwise
            if not mainPoly.PolyIsClockwise():
                mainPoly = mainPoly.ReverseLineDirections()
            # Start the main poly from a point close to the start of the path
            origStartPoint = pointsIn[0]
            distances = [(x[0]-origStartPoint[0])**2+(x[1]-origStartPoint[1])**2 for x in mainPoly.points]
            minDist = min(distances)
            ndx = distances.index(minDist)
            l = mainPoly.points[ndx:] + mainPoly.points[:ndx]
            mainPoly = Blender4CNC.Polytoxogon(l)
            # Make sure the tenons are counter clockwise
            for i in range(0,len(tenons)):
                tenon = tenons[i]
                if tenon.PolyIsClockwise():
                    tenons[i] = tenon.ReverseLineDirections()

#            return (mainPoly, tenons, totalInvalidPolyList)
            return (mainPoly, tenons)


        #********************************************************************
        # A capsule becomes just 3 lines to the "left" of the original line
        #********************************************************************
        def CreateHalfPoly(self, origSeg, dist):
            endV = self.GetSegVectorAtPoint(origSeg, origSeg[1][0:2])
            startV = self.GetSegVectorAtPoint(origSeg, origSeg[0][0:2])
            startV = (-startV[0], -startV[1], -startV[2])
            #r = self.GetArcRadius(origSeg)
            d = dist*2
            endV = (endV[0]*d, endV[1]*d)
            startV = (startV[0]*d, startV[1]*d)
            endSeg = (origSeg[1][0:2], (endV[0]+origSeg[1][0], endV[1]+origSeg[1][1]))
            startSeg = (origSeg[0][0:2], (startV[0]+origSeg[0][0], startV[1]+origSeg[0][1]))
            int0 = self.GetIntersectionsBetweenLineAndArc(startSeg, self.lines[0])[0]
            int2 = self.GetIntersectionsBetweenLineAndArc(endSeg, self.lines[2])[0]
            int2 = int2 + self.lines[2][1][2:]
            ret = Blender4CNC.Polytoxogon([int0, self.lines[0][1], self.lines[1][1], int2])
            return ret
        #********************************************************************
        def ExpandSingleSegmentToCapsuleStraight(self, seg, dist):
            right = self.GetParallelLine(seg, dist)
            revSeg = (seg[1], seg[0])
            left = self.GetParallelLine(revSeg, dist)
            (a,b) = seg
            (c,d) = right
            (e,f) = left
            c1 = (c[0], c[1], a[0], a[1], -1)                
            e1 = (e[0], e[1], b[0], b[1], -1)               
            p1 = f
            p2 = c1
            p3 = d
            p4 = e1
            return Blender4CNC.Polytoxogon([p1,p2,p3,p4])
        #********************************************************************
        def ExpandSingleSegmentToCapsule(self, seg, dist):
            poly = self.ExpandSingleSegmentToCapsuleCCW(seg, dist)
            poly = poly.ReverseLineDirections()
            points = poly.points[-1:] + poly.points[:-1]
            poly = Blender4CNC.Polytoxogon(points)
            return poly
        #********************************************************************
        def ReverseArcSegment(self, seg):
            (a,b) = seg
            p = a[0:2] + b[2:4] + (-b[4],)
            return (b,p)
        #********************************************************************
        def ExpandSingleSegmentToCapsuleCCW(self, seg, dist):
            if self.PointIsStraight(seg[1]):
                return self. ExpandSingleSegmentToCapsuleStraight(seg, dist)
            else:
                #print("seg=", seg)
                FEQ = Blender4CNC.FloatsAreEqual
                revSeg = self.ReverseArcSegment(seg)
                foreSeg = self.ReverseArcSegment(revSeg)
                right = self.GetParallelCurve(foreSeg, dist)
                left = self.GetParallelCurve(revSeg, dist)
                (a,b) = foreSeg
                (c,d) = right
                (e,f) = left
                #print("foreSeg, revSeg, right, left=", foreSeg, revSeg, right, left)
                # Check if a CW curve has shrunk down to nothing on the right side
                if (foreSeg[1][4] == 1) and FEQ(c[0], d[0]) and FEQ(c[1], d[1]):
                    f_a = (a[0]-f[0], a[1]-f[1])
                    newC = (a[0] + f_a[0], a[1] + f_a[1])
                    newC = newC[0:2] + a[0:2] + (-1,)
                    newF = f[0:2] + a[0:2] + (-1,)
                    arc1 = (newF, newC)

                    e_b = (b[0]-e[0], b[1]-e[1])
                    newD = (b[0] + e_b[0], b[1] + e_b[1])
                    newD = newD[0:2] + b[0:2] + (-1,)
                    newE = e[0:2] + b[0:2] + (-1,)
                    arc2 = (newD, newE)

                    ints = self.GetIntersectionsBetweenTwoArcs(arc1, arc2)
                    (inta,intb) = ints[0]
                    if FEQ(inta,0):
                        inta = 0
                    if FEQ(intb,0):
                        intb = 0
                    p = (inta,intb)
                    
                    p1 = f
                    p2 = p + a[0:2] + (-1,)
                    p3 = newE
                    return Blender4CNC.Polytoxogon([p1,p2,p3])
                # Check if a CCW curve has shrunk down to nothing on the left side
                elif (foreSeg[1][4] == -1) and FEQ(e[0], f[0]) and FEQ(e[1], f[1]):
                    c_a = (a[0]-c[0], a[1]-c[1])
                    newF = (a[0] + c_a[0], a[1] + c_a[1])
                    newC = c[0:2] + a[0:2] + (-1,)
                    arc1 = (newF, newC)
                    
                    d_b = (b[0]-d[0], b[1]-d[1])
                    newE = (b[0] + d_b[0], b[1] + d_b[1])
                    newE = newE + b[0:2] + (-1,)
                    arc2 = (d, newE)
                    
                    ints = self.GetIntersectionsBetweenTwoArcs(arc1, arc2)
                    (inta,intb) = ints[0]
                    if FEQ(inta,0):
                        inta = 0
                    if FEQ(intb,0):
                        intb = 0
                    p = (inta,intb)
                    
                    p1 = p + b[0:2] + (-1,)
                    p2 = newC
                    p3 = d
                    return Blender4CNC.Polytoxogon([p1,p2,p3])
                else:
                    p1 = f
                    p2 = c[0:2] + a[0:2] + (-1,)
                    p3 = d
                    p4 = e[0:2] + b[0:2] + (-1,)
                    return Blender4CNC.Polytoxogon([p1,p2,p3,p4])
        #********************************************************************
        def Convert3SegPolysTo4SegPolys(self, polyListPoints, polyList):
            for i,poly in enumerate(polyList):
                if len(poly.lines) == 3:
                    curve = polyListPoints[i]
                    #print("curve=", curve)
                    (a,b) = curve
                    if b[4] == 1:
                        #print("CW")
                        # CW curve - we must put in a dummy seg 3
                        p = poly.lines[2][1][0:2]
                        poly.lines.append((p,p))
                    else:
                        #print("CCW")
                        # CCW curve - must put in a dummy seg 1
                        p = poly.lines[0][1][0:2]
                        #print("poly.lines=", poly.lines)
                        #print("p=", p)
                        poly.lines.insert(1,(p,p))
                        #print("poly.lines=", poly.lines)
            return polyList            
        #********************************************************************
        def Find2PointsCloseToIntersection(self, curPoly, curSegNdx, nextPoly, hitSeg, intP, dist):
            FEQ = Blender4CNC.FloatsAreEqual
            curSeg = curPoly.lines[curSegNdx]
            nextSeg = nextPoly.lines[hitSeg]
            isCurve = False
            if len(nextSeg[1]) > 2:
                isCurve = True
            # Find two points that are close to the intersection
            extra = nextSeg[1][2:]
            if isCurve:
                intP = intP[0:2] + extra
            else:
                intP = intP[0:2]
            limit = dist/10
            segA = (nextSeg[0][0:2], intP)
            segB = (intP, nextSeg[1])
            # If segA is a curve and we have made it so that the start point is the same as the end point,
            # the GetLengthOfSegment function will measure it as a "full circle"
            if FEQ(segA[0][0], segA[1][0]) and FEQ(segA[0][1], segA[1][1]):
                dA = 0
            else:
                dA = self.GetLengthOfSegment(segA)
            while dA > limit:
                p = self.GetMidOfSegment(segA)
                p = p[0:2]
                segA = (p, intP)
                dA = self.GetLengthOfSegment(segA)

            if FEQ(segB[0][0], segB[1][0]) and FEQ(segB[0][1], segB[1][1]):
                dB = 0
            else:
                dB = self.GetLengthOfSegment(segB)
            while dB > limit:
                p = self.GetMidOfSegment(segB)
                if isCurve:
                    p = p[0:2] + extra
                else:
                    p = p[0:2]
                segB = (intP, p)
                dB = self.GetLengthOfSegment(segB)
            return (segA[0], segB[1])
        #********************************************************************
        # The nextSeg intersects with curSeg at point intP.
        # Is it going from "inside" the curPoly to "outside"?
        # I.e. Is it "moving away"?
        # OR Is it a tangent?
        # Choose two points very close to the intersection, but on either
        # side and determine if they are inside or outside the curPoly
        # Returns 1 for "moving away", 2 for tangent, 0 otherwise
        #********************************************************************
        def SegmentIsMovingAwayOrTangent(self, curPoly, curSegNdx, nextPoly, hitSeg, intP, dist, curFullPoly):
            curSeg = curPoly.lines[curSegNdx]
            nextSeg = nextPoly.lines[hitSeg]

            (p1, p2) = self.Find2PointsCloseToIntersection(curPoly, curSegNdx, nextPoly, hitSeg, intP, dist)

            startsOnBoundary = curPoly.IsPointOnBoundary(p1)
            endsOnBoundary = curPoly.IsPointOnBoundary(p2)

            # Find whether points are inside/outside
            # We choose to say that a point on the boundary is considered to be inside
            if startsOnBoundary:
                insideA = True
            else:
                insideA = curFullPoly.IsPointInside(p1)
            if endsOnBoundary:
                insideB = True
            else:
                insideB = curFullPoly.IsPointInside(p2)
            
            # If the point prior to the intersection is inside and
            # the point after the intersection is outside, then we
            # are moving away (all else is moving in or a tangent)
            if insideA and not insideB:
                return 1
            elif not insideA and not insideB:
                return 2
            else:
                return 0
                
        #********************************************************************
        def RightLeftFromPath(self, pointsIn, dist, right):

            if Blender4CNC.REGRESSION_TEST_DRAW_OUTPUTS:
                # FAILS COVERAGE
                Blender4CNC.DRAW_OUTPUTS_inputPath = pointsIn
                Blender4CNC.DRAW_OUTPUTS_outputPath = []
                Blender4CNC.DRAW_OUTPUTS_segmentPolys = []

            # If there is just one point then this is just a hole
            if len(pointsIn) == 1:
                raise Blender4CNC.PolyException("Cannot create path from a single point", (pointsIn[0][0], pointsIn[0][1]))

            # If there are just two points and they are the same X,Y and the 2nd point is a curve, then this is a circle
            if (len(pointsIn) == 2) and self.PointsAreEqual(pointsIn[0], pointsIn[1]):
                raise Blender4CNC.PolyException("Cannot create path from a circle", (pointsIn[0][0], pointsIn[0][1]))

            FEQ = Blender4CNC.FloatsAreEqual
            # Convert each pair of points to a poly
            polyListPoints = [pointsIn[i:i+2] for i in range(0,len(pointsIn)-1)]

            # Everything in this routine works to the left of a path, to go right, we:
            # 1) Reverse the path
            # 2) Calculate the offset path
            # 3) Reverse the result
            if right:
                # Reverse the input points
                polyListPoints2 = []
                for seg in polyListPoints:
                    if len(seg[1]) == 2:
                        newSeg = (seg[1], seg[0][0:2])
                    else:
                        newSeg = self.ReverseArcSegment(seg)
                    polyListPoints2.append(newSeg)
                polyListPoints2.reverse()
                polyListPoints = polyListPoints2

            (changed, newLines) = self.SplitUpLargeCurvesSub(polyListPoints)
            if changed:
                polyListPoints = newLines
            #print("polyListPoints=", polyListPoints)
            flatList = [(seg[0][0:2], seg[1]) if len(seg[1]) == 2 else ((seg[0][0], seg[0][1], seg[1][2], seg[1][3], -seg[1][4]), seg[1]) for seg in polyListPoints]
            flatList = [Blender4CNC.Polytoxogon(x) for x in flatList]
            #print("flatList=", flatList)
            # Expand the "zero-area" polys to expanded capsule polys
            # Watch out, Expand reverses things...
            # polyList = [poly.Expand(None, dist)[0] for poly in flatList]
            polyList = [self.ExpandSingleSegmentToCapsule(seg, dist) for seg in polyListPoints]
            polyList = self.Convert3SegPolysTo4SegPolys(polyListPoints, polyList)
            halfPolyList = []
            for i,poly in enumerate(polyList):
                halfPoly = poly.CreateHalfPoly(polyListPoints[i], dist)
                halfPolyList.append(halfPoly)


            # Define some command states
            (MOVE_TO_NEXT_SEG, MOVE_TO_NEXT_POLY, MOVE_ERROR) = (1,2,3)
            
            curPolyNdx = 0
            curSegNdx = 0
            points = []
            while curPolyNdx < (len(polyList)-1):
                curPoly = halfPolyList[curPolyNdx]
                curFullPoly = polyList[curPolyNdx]
                curSeg = curPoly.lines[curSegNdx]
                nextPoly = halfPolyList[curPolyNdx+1]
                
                CMD = -1
                
                # Is current segment a point?
                (a,b) = curSeg
                if a == b:
                    CMD = MOVE_TO_NEXT_SEG
                elif curSegNdx in [0,1]:
                    hitSeg = 2
                    nextSeg = nextPoly.lines[hitSeg]
                    # Find where the current segment might hit either seg 1 or 2 in the next poly
                    ints = self.GetAllIntersections(curSeg, nextSeg)
                    if (ints == None) or ((ints != inf) and (len(ints)==0)):
                        # Current segment did not hit seg 2 in next poly, try seg 1
                        hitSeg = 1
                        nextSeg = nextPoly.lines[hitSeg]
                        (a,b) == nextSeg
                        if a != b:
                            ints = self.GetAllIntersections(curSeg, nextSeg)
                    if (ints == None) or ((ints != inf) and (len(ints)==0)):
                        CMD = MOVE_TO_NEXT_SEG
                    else:
                        if (ints == inf) and (curSegNdx == 0) and (hitSeg == 2):
                            # If curPoly seg 0 overlaps nextPoly seg 2
                            ints = self.GetOverlap(curSeg, nextSeg)
                            # Sort the list of intersections along the segment
                            ints = self.OrderIntersections(curSeg, ints)
                            intP = ints[1]
                            if len(curSeg[1]) > 2:
                                intP = intP + curSeg[1][2:]
                            CMD = MOVE_TO_NEXT_POLY
                        else:    
                            # Sort the list of intersections along the segment
                            ints = self.OrderIntersections(curSeg, ints)
                            intP = ints[0]
                            (a,b) = intP[0:2]
                            (p1,p2) = nextSeg
                            (c,d) = p1[0:2]
                            if FEQ(a, c) and FEQ(b, d):
                                # intersection = start of the next poly segment
                                if len(curSeg[1]) > 2:
                                    intP = intP + curSeg[1][2:]
                                CMD = MOVE_TO_NEXT_POLY
                            else:
                                movingAway = self.SegmentIsMovingAwayOrTangent(curPoly, curSegNdx, nextPoly, hitSeg, intP, dist, curFullPoly)
                                if movingAway == 1: # Moving away
                                    if len(curSeg[1]) > 2:
                                        intP = intP + curSeg[1][2:]
                                    CMD = MOVE_TO_NEXT_POLY
                                elif movingAway == 2: # Tangent
                                    CMD = MOVE_TO_NEXT_SEG
                                else:
                                    CMD = MOVE_ERROR
                else: # current segment must be equal to 2
                    hitSeg = 0
                    nextSeg = nextPoly.lines[hitSeg]
                    ints = self.GetAllIntersections(curSeg, nextSeg)
                    if (ints == None) or ((ints != inf) and (len(ints)==0)):
                        CMD = MOVE_ERROR
                    else:
                        (a,b) = nextSeg
                        if (ints != inf) and FEQ(ints[0][0], a[0]) and FEQ(ints[0][1], a[1]):
                            # intersection is equal to the start of the next poly segment 0
                            intP = ints[0]
                            if len(curSeg[1]) > 2:
                                intP = intP + curSeg[1][2:]
                            CMD = MOVE_TO_NEXT_POLY
                        else: # it must overlap
                            overlap = self.GetOverlap(curSeg, nextSeg)
                            intP = overlap[1]
                            CMD = MOVE_TO_NEXT_POLY
                            
                # Now handle the commands
                if CMD == MOVE_ERROR:
                    raise Blender4CNC.PolyException("Malformed points on path", curSeg[0])
                elif CMD == MOVE_TO_NEXT_SEG:
                    points.append(curSeg[1])
                    curSegNdx += 1
                else: # CMD == MOVE_TO_NEXT_POLY:
                    if len(points) == 0:
                        points.append(intP)
                    else:
                        (a,b) = points[-1][0:2]
                        (c,d) = intP[0:2]
                        if not (FEQ(a,c) and FEQ(b,d)):
                            points.append(intP)
                    curPolyNdx += 1
                    curSegNdx = hitSeg
                    (a,b) = halfPolyList[curPolyNdx].lines[curSegNdx]
                    halfPolyList[curPolyNdx].lines[curSegNdx] = (intP, b)
            # End of while

            # Add endpoints of all segments up to and including the hitSeg
            curPoly = polyList[curPolyNdx]
            for i in range(curSegNdx, 2):
                a = points[-1]
                p = curPoly.lines[i][1]
                if not (FEQ(a[0], p[0]) and FEQ(a[1], p[1])):
                    points.append(p)
            
            # Remove any duplicates
            newPoints = [points[i] for i in range(0,len(points)-1) if points[i] != points[i+1]] + [points[-1]]
            points = newPoints
            
            # Make the start point simple
            points[0] = points[0][0:2]

            poly = Blender4CNC.Polytoxogon(points)

            poly.RemoveSuperfluousCurve()

            if right:
                poly = poly.ReverseLineDirections()
                # Then put first point at end
                points = poly.points[1:] + [poly.points[0]]
                poly = Blender4CNC.Polytoxogon(points)
                
            # Remove any duplicates
            points = poly.points
            newPoints = [points[i] for i in range(0,len(points)-1) if points[i] != points[i+1]] + [points[-1]]
            points = newPoints

            if Blender4CNC.REGRESSION_TEST_DRAW_OUTPUTS:
                # FAILS COVERAGE
                Blender4CNC.DRAW_OUTPUTS_outputPath = points
                Blender4CNC.DRAW_OUTPUTS_segmentPolys = polyList

            return points
        
        #********************************************************************
        # Check if the poly (tenon2) Will be totally inside this poly
        # when the poly is expanded by dist.
        #********************************************************************
        def WillBeCompletelyInside(self, tenon2, dist):
            polyTenons = self.Expand(None, dist)
            # We just ignore any tenons for now
            (poly, tenons) = polyTenons
            (poly1, poly2) = poly.Create2PolysFromCutLines(tenon2)
            return poly1.IsPolyCompletelyInside(poly2)

        #********************************************************************
        # Returns a new list where ALL polys are in clockwise order!
        # DOES NOT deal with any newly created tenons!!!!!!!
        def JoinOverlappingPolys(self, l):

            # Ensure all polys are clockwise (for join)
            finalTenonsList = []
            for poly in l:
                if not poly.PolyIsClockwise():
                    poly = poly.ReverseLineDirections()
                finalTenonsList.append(poly)

            i = 0
            while i < len(finalTenonsList):
                poly = finalTenonsList[i]
                    
                # Find if this poly overlaps with any other poly
                j = i + 1
                newPoly = None
                while j < len(finalTenonsList):
                    polyJ = finalTenonsList[j]

                    if not poly.BoundingRectanglesOverlap(polyJ):
                        j += 1
                        continue
                    
                    if not poly.Overlap(polyJ):
                        j += 1
                        continue
                    
                    # They overlap, so join them
                    # Because tenons are in CCW order, the join function will not return a main poly
                    polyTenonList = poly.Add(polyJ)
                    newPoly = polyTenonList[0][0]
                    # Replace the poly with the new joined poly
                    finalTenonsList[i] = newPoly
                    finalTenonsList.pop(j)
                    poly = newPoly
                    # End j loop
                i += 1
            # End i loop
            return finalTenonsList

        #********************************************************************
        # 
        #********************************************************************
        def RemoveOverlapPolysFromTenons(self, tenons, overlapPolys):
            finalTenons = []
            while len(tenons) > 0:
                tenon = tenons.pop(0)
                result = [tenon]
                for overlapPoly in overlapPolys:
                    result = tenon.Subtract(overlapPoly)
                    # Subtraction will never give us any "tenons" from the polys
                    result = [x[0] for x in result]
                    if (len(result) == 0) or (result == [None]):
                        # The tenon is completely gone
                        break
                    elif len(result) == 1:
                        tenon = result[0]
                    else:
#                        tenons = [result[0][0]]
                        # The tenon got split up
                        tenons += result
                        break
                if len(result) == 1:
                    finalTenons.append(result[0])                        
            return finalTenons
        #********************************************************************
        # Returns True if this poly has no area - all lines exactly overlap
        # other lines
        #********************************************************************
        def IsPureOverlapPoly(self):
            linesAndInts = self.GetIntersectionsBetweenAllLines(self.lines)
            for k in linesAndInts.keys():
                l = linesAndInts[k]
                # See if this segment has an infinite overlap that is complete
                coords = self.lines[k]
                coords = [x[0:2] for x in coords]
                completeOverlap = False
                for item in l:
                    (otherLine, intersections) = item
                    if intersections[0] == inf:
                        intersections = intersections[1]
                        intersections = [x[0:2] for x in intersections]
                        a = coords
                        b = intersections
                        if (a[0] in b) and (a[1] in b):
                            completeOverlap = True
                            break
                if completeOverlap:
                    linesAndInts[k] = []
                    linesAndInts[otherLine] = []
            l = list(linesAndInts.items())
            l = [x[1] for x in l]
            for item in l:
                if item != []:
                    return False
            return True
        #********************************************************************
        # Join together overlapping stubs with polys that have area 
        # and
        # join together polys that are bridged by overlapping "no-area" polys
        # and 
        # join together any polys that touch (even if not by a "no-area" poly)
        # and 
        # join together any overlapping "no-area" polys
        #
        # Note that the Shrink function can generate clockwise and counter-clockwise
        # polys - it must filter out the non-needed CCW polys before calling this
        # function
        #
        # EXAMPLE 1
        #              b--c            b--c
        #              |  |            |  |
        # x--a   AND   a--d becomes x--a--d
        #
        # EXAMPLE 2
        # b--c                      f--g         b--c  f--g
        # |  |                      |  |         |  |  |  |
        # a--d   AND   d--e   AND   e--h becomes a--d--e--h
        #
        # EXAMPLE 3    e--f                e--f
        #              |  |                |  |
        # b--c   AND   c--g   becomes   b--c--g
        # |  |                          |  |
        # a--d                          a--d
        #
        # EXAMPLE 4
        #   b       b                 b    b
        #  /         \               /      \
        # a   AND     c   stays     a        c
        #********************************************************************
        def JoinMultipleTouchingPolys(self, listOfPolys):

            listOfOverlapPolys = [poly for poly in listOfPolys if poly.IsPureOverlapPoly()]
            listOfNormalPolys = list(set(listOfPolys) - set(listOfOverlapPolys))
                
            changed = True
            while changed:
                changed = False
                    
                for i in range(0,len(listOfOverlapPolys)):
                    setA = set([p[0:2] for p in listOfOverlapPolys[i].points])
                    # Find if this overlap poly touches one or two normal polys
                    touchList = []
                    for j in range(0,len(listOfNormalPolys)):
                        setB = set([p[0:2] for p in listOfNormalPolys[j].points])
                        ints = setA.intersection(setB)
                        if len(ints) > 0:
                            # These two polys are to be connected
                            touchList.append(j)
                    # The following condition *should* never happen
                    #if len(touchList) > 2:
                    #    MULTIPLE_POLYS_INTERSECT_OVERLAP_POLY
                    if len(touchList) >= 1:
                        changed = True
                        polyA = listOfOverlapPolys[i]
                        polyB = listOfNormalPolys[touchList[0]]
                        # In this circumstance, all are clockwise
                        polyD = polyA.Add(polyB, -1, True, True, True)
                        # Under this circumstance, where this function is only ever called from a place
                        # in Shrink, there will never be multiple polys or tenons
                        polyD = polyD[0][0]
                        if len(touchList) == 2:
                            polyC = listOfNormalPolys[touchList[1]]
                            polyD = polyD.Add(polyC, -1, True, True, True)
                            polyD = polyD[0][0]
                            listOfNormalPolys.pop(touchList[1])
                        listOfOverlapPolys.pop(i)
                        listOfNormalPolys.pop(touchList[0])
                        listOfNormalPolys.append(polyD)
                        break
            # It is possible that some of the "normal" polys are touching
            # Valid polys are clockwise, so ignore counterclockwise polys
            # ONLY PASS CLOCKWISE POLYS INTO THIS FUNCTION!
            changed = True
            while changed:
                changed = False
                for i in range(0,len(listOfNormalPolys)):
#                    if not listOfNormalPolys[i].PolyIsClockwise():
#                        continue
                    setA = set([p[0:2] for p in listOfNormalPolys[i].points])
                    # Find if this poly touches another poly
                    for j in range(i+1,len(listOfNormalPolys)):
#                        if not listOfNormalPolys[j].PolyIsClockwise():
#                            continue
                        setB = set([p[0:2] for p in listOfNormalPolys[j].points])
                        ints = setA.intersection(setB)
                        if len(ints) > 0:
                            # These two polys are to be connected
                            polyA = listOfNormalPolys[i]
                            polyB = listOfNormalPolys[j]
                            common = list(ints)[0]
                            pointsA2D = [p[0:2] for p in polyA.points]
                            pointsB2D = [p[0:2] for p in polyB.points]
                            ndxA = pointsA2D.index(common)
                            ndxB = pointsB2D.index(common)
                            points = polyA.points[:ndxA+1] + polyB.points[ndxB+1:] + polyB.points[:ndxB+1] + polyA.points[ndxA+1:]
                            listOfNormalPolys.pop(j)
                            listOfNormalPolys.pop(i)
                            listOfNormalPolys.append(Blender4CNC.Polytoxogon(points))
                            changed = True
                            break
                    if changed:
                        break
                            
            listOfPolys = listOfOverlapPolys + listOfNormalPolys
            return listOfPolys
        def Shrink(self, dist, infiniteLoopCount = -1):
            
            s = ""
            pt = self.points[0] # All points might get removed and then an exception occurs
                                # so we store this here
            if infiniteLoopCount == -1:
                infiniteLoopCount = 1000
                
            self.CleanUpPoly_UI()
                
            if not self.ImPolyIsClockwise():
                str2 = "ERROR - Cannot shrink counter-clockwise poly by " + str(dist) + "."
                raise Blender4CNC.PolyException(str2, self.points[0])

            try:
                # In case of overlapping lines, we must split the poly
                polys = self.SplitPolyOnInfiniteOverlaps()
                # Identify all the overlapped polys vs "normal" polys
                normalPolys = []
                for poly in polys:
                    if len(poly.lines) == 2:
                        # Could be an overlap pair
                        if self.GetAllIntersections(poly.lines[0], poly.lines[1]) == inf:
                            normalPolys.append(False)
                            continue
                    normalPolys.append(True)
                # Check if ALL polys have no area - the poly would get shrunk to nothing
                if True not in normalPolys:
                    str2 = "ERROR - Cannot shrink poly by " + str(dist) + ". Poly too thin?\n"
                    raise Blender4CNC.PolyException(str2, self.points[0])
                
                # Identify all the overlapped polys vs "normal" polys
                normalPolys = []
                for poly in polys:
                    if len(poly.lines) == 2:
                        # Could be an overlap pair
                        if self.GetAllIntersections(poly.lines[0], poly.lines[1]) == inf:
                            normalPolys.append(False)
                            continue
                    normalPolys.append(True)
                # We shrink all the polys separately
                newPolys = [poly.ShrinkExpandAndSplit(dist, -1) for poly in polys]
                # If nothing left...
                if newPolys == [[]]:
                    raise Blender4CNC.PolyException(" ", (0,0))

                
                # In certain scenarios, a poly can get shrunk and what is returned is multiple polys
                # where some of the returned polys are "zero area" polys that need to be joined to 
                # other "normal" polys
                for k,listOfPolys in enumerate(newPolys):
                    if len(listOfPolys) <= 1:
                        continue
                    # Filter out any CCW polys first
                    polysToJoin = []
                    for poly in listOfPolys:
                        if poly.ImPolyIsClockwise():
                            polysToJoin.append(poly)
                    newPolys[k] = self.JoinMultipleTouchingPolys(polysToJoin)
                                
                # ShrinkExpandAndSplit always returns a list of polys
                # [ poly1, poly2, poly3 ... ]
                # When expanding - This may represent a main poly with tenons and invalid loops
                # When shrinking - It may represent multiple polys and invalid loops
                #                  (valid polys are clockwise)
                #                   [ [poly1], [poly2,poly3], [poly4] ... ]
                newPolys2 = []
                for l in newPolys:
                    validPolys = [poly for poly in l if poly.ImPolyIsClockwise()]
                    newPolys2.append(l)
                newPolys = newPolys2

                # Get the shrunken normal polys
                polys = []
                overlapPolys = []
                for i,tf in enumerate(normalPolys):
                    if tf:
                         polys.append(newPolys[i])
                    else:
                        overlapPolys.append(newPolys[i])
                # All the "non-normal" polys need to be subtracted from any "normal" polys

                # Arrange polys into a simple list of polys (not a list of lists)
                polys = [item for l in polys for item in l]
                overlapPolys = [item for l in overlapPolys for item in l]
                for i,poly in enumerate(overlapPolys):
                    if not poly.ImPolyIsClockwise():
                        poly = poly.ReverseLineDirections()
                        overlapPolys[i] = poly
#                    if len(polys) > 0:
#                        print(polys[0].PolyIsClockwise())
#                    if len(overlapPolys) > 0:
#                        print(overlapPolys[0].PolyIsClockwise())
                ret = self.RemoveOverlapPolysFromTenons(polys, overlapPolys)
                newPolys = ret
#                if len(ret) != 1:
#                    str2 = "ERROR - Cannot shrink/expand poly by " + str(dist) + ".\nDetected split areas.\nCutter too large?"
#                    raise Blender4CNC.PolyException(str2, (0,0))
#                else:
#                    poly = ret[0]
            except Blender4CNC.PolyException as err:
                s = err.args[0]

            if len(s) > 0:
                str2 = "ERROR - Cannot shrink poly by " + str(dist) + ". Poly too thin?\n" + s
                raise Blender4CNC.PolyException(str2, (self.points[0][0],self.points[0][1]))
                # Do not think the following code is necessary anymore
                #if len(self.points) > 0:
                #    raise Blender4CNC.PolyException(str2, (self.points[0][0],self.points[0][1]))
                #else:
                #    raise Blender4CNC.PolyException(str2, (pt[0], pt[1]))

            # Clean up all the polys
            for poly in newPolys:
                poly.CleanUpPoly_UI()

            # Arrange the polys so they start closest to the original poly start point
            for poly in newPolys:
                poly.MakePolyStartClosestToPoint(pt)
            # Order the polys as closest to the original start point
            a = self.points[0]
            distances = []
            for poly in newPolys:
                b = poly.points[0]
                d = (b[0]-a[0])**2 + (b[1]-a[1])**2
                distances.append(d)
            newPolys2 = []
            while len(distances) > 0:
                minDist = min(distances)
                ndx = distances.index(minDist)
                newPolys2.append(newPolys.pop(ndx))
                distances.pop(ndx)
                    
            return newPolys2

        def GetLargestPolyAndIndex(self, polys):
            bounds = [poly.GetBoundingRectangle() for poly in polys]
            areas = [(x[2]-x[0])*(x[3]-x[1]) for x in bounds]
            maxArea = max(areas)
            maxNdx = areas.index(maxArea)
            return (polys[maxNdx], maxNdx)
        def GetPointAndIndexClosestTo(self, origStartPoint):
            mins = {}
            distances = []
            for j, point in enumerate(self.points):
                dX = point[0] - origStartPoint[0]
                dY = point[1] - origStartPoint[1]
                dSquared = dX**2 + dY**2
                distances.append(dSquared)
            minD = min(distances)
            minNdx = distances.index(minD)
            return (self.points[minNdx], minNdx)
        #********************************************************************
        # 
        #********************************************************************
        def SplitUpLargeCurves(self):
            newLines = []
            changed = False
            (changed, newLines) = self.SplitUpLargeCurvesSub(self.lines)
            if not changed:
                return self
            else:
                points = [x[1] for x in newLines]
                points = [points[-1]] + points[:-1]
                return Blender4CNC.Polytoxogon(points)
        #********************************************************************
        def SplitUpLargeCurvesSub(self, lines):
            newLines = []
            changed = False
            for i,line in enumerate(lines):
                if len(line[1]) == 2:
                    newLines.append(line)
                else:
                    a = line[0][0:2]
                    b = line[1][0:2]
                    center = line[1][2:4]
                    vA = (a[0] - center[0], a[1] - center[1])
                    vB = (b[0] - center[0], b[1] - center[1])
                    CW = line[1][4]
                    if CW == 1:
                        angle = self.GetClockwiseAngleBetweenVectors(vA, vB)
                    else:
                        angle = -self.GetClockwiseAngleBetweenVectors(vB, vA)
                    if abs(angle) <= math.pi:
                        newLines.append(line)
                    else:
                        # Must split curve (remember RotateVector goes CCW)
                        changed = True
                        if (CW == 1):
                            vC = self.RotateVector(vB, angle/2)
                        else:
                            # For CCW, must negate angle
                            vC = self.RotateVector(vA, -angle/2)
                        vC = (vC[0] + center[0], vC[1] + center[1])
                        midPoint = (vC[0], vC[1], center[0], center[1], CW)
                        lineA = (line[0], midPoint)
                        lineB = (midPoint, line[1])
                        newLines.append(lineA)
                        newLines.append(lineB)
            return (changed, newLines)
        #********************************************************************
        # Returns a Polytoxogon that has been expanded by dist.
        #********************************************************************
        def Expand(self, p2g, dist, infiniteLoopCount=1000):

            # Clean the Poly 
            self.CleanUpPoly_UI()

            if not self.ImPolyIsClockwise():
                str2 = "ERROR - Cannot expand counter-clockwise poly by " + str(dist) + "."
                raise Blender4CNC.PolyException(str2, self.points[0])

#            # Any curve that is larger than 180 degrees must be split in half
#            poly = self.SplitUpLargeCurves()
#            if poly != self:
#                self.points = poly.points
#                self.lines = poly.lines

            # In case of overlapping lines, we must split the poly
            polys = self.SplitPolyOnInfiniteOverlaps()

            # We expand all the polys separately
            newPolys = []
            for poly in polys:
                # Make it CCW so we get an expand
                poly = poly.ReverseLineDirections()
                polyTenons = poly.ShrinkExpandAndSplit(dist, -1)
                    
                # ShrinkExpand may return multiple polys, when expanding, the "main" poly will be the
                # largest and it will be CCW
                (mainPoly, mainNdx) = self.GetLargestPolyAndIndex(polyTenons)
                # Make it CW again
                mainPoly = mainPoly.ReverseLineDirections()
                # Find any "tenons" that touch the main poly - these are invalid loops
                polyTenons.pop(mainNdx)
                validTenons = []
                mainPolyPoints2D = [(x[0], x[1]) for x in mainPoly.points]
                setMain = set(mainPolyPoints2D)
                for poly in polyTenons:
                    aPoints2D = [(x[0], x[1]) for x in poly.points]
                    setA = set(aPoints2D)
                    setB = setA.intersection(setMain)
                    if len(setB) > 0:
                        # This is invalid internal poly
                        continue
                    else:
                        validTenons.append(poly)

                newPolyTenons = [mainPoly, validTenons]
                newPolys.append(newPolyTenons)

            # Identify all the overlapped polys vs "normal" polys
            normalPolys = []
            for poly in polys:
                if len(poly.lines) == 2:
                    # Could be an overlap pair
                    if self.GetAllIntersections(poly.lines[0], poly.lines[1]) == inf:
                        normalPolys.append(False)
                        continue
                normalPolys.append(True)
            # All the "normal" polys and "non-normal" polys need to be added together while the 
            # "non-normal" polys need to be subtracted from any tenons
            # Tenons may be produced when adding the polys together!
            polysToBeAdded = [x[0] for x in newPolys]
            tenons = []
            finalPoly = polysToBeAdded.pop(0)
            polysToBeAdded2 = []
            loopCount = 0
            while len(polysToBeAdded) > 0:
                changed = False
                while len(polysToBeAdded) > 0:
                    loopCount += 1
                    if loopCount > infiniteLoopCount:
                        str2 = "ERROR - Expand function stuck in infinite loop."
                        raise Blender4CNC.PolyException(str2, (0,0))
                    poly2Add = polysToBeAdded.pop(0)
                    if finalPoly.Overlap(poly2Add):
                        temp = finalPoly.Add(poly2Add, -1, True, True, True)
                        finalPoly = temp[0][0]
                        tenons += temp[0][1]
                        changed = True
                    else:
                        polysToBeAdded2.append(poly2Add)
                polysToBeAdded = polysToBeAdded2
                if not changed:
                    break

            # All should now be added together into finalPoly
            # We must now deal with the tenons
            # Note, it is possible for an overlap to have created a tenon for itself
            # like a curve that is *nearly* a circle
            overlapPolys = []
            allTenons = tenons
            for i in range(0,len(newPolys)):
                if not normalPolys[i]:
                    overlapPolys.append(newPolys[i][0])
                allTenons += newPolys[i][1]
            # To get ready to subtract them, must make sure all polys are clockwise
            for i,poly in enumerate(allTenons):
                if not poly.PolyIsClockwise():
                    allTenons[i] = poly.ReverseLineDirections()
            for i,poly in enumerate(overlapPolys):
                if not poly.PolyIsClockwise():
                    # FAILS COVERAGE
                    overlapPolys[i] = poly.ReverseLineDirections()
                  
            finalTenons = self.RemoveOverlapPolysFromTenons(allTenons, overlapPolys)

            # Clean the Poly and any tenons
            finalPoly.CleanUpPoly_UI()
            for i in range(0,len(finalTenons)):
                tenon = finalTenons[i]
                tenon.CleanUpPoly_UI()
                finalTenons[i] = tenon

            # We want to find the point that is closest to the original starting point
            # Re-arrange that poly so that that particular point
            # is the starting point of the poly
            finalPoly.MakePolyStartClosestToPoint(self.points[0])
            
            return [finalPoly, finalTenons]

        #********************************************************************
        # Gets the CW/CCW value of the curve (1=CW, -1 = CCW)
        #********************************************************************
        def MakePolyStartClosestToPoint(self, origStart):
            (closestPoint, closestNdx) = self.GetPointAndIndexClosestTo(origStart)
            self.points = self.points[closestNdx:] + self.points[:closestNdx]
            self.lines = self.GetListOfLinesFromPoints(self.points)

        #********************************************************************
        # Gets the CW/CCW value of the curve (1=CW, -1 = CCW)
        #********************************************************************
        def GetCurveClockwiseness(self, seg):
            return seg[1][4]
        
        #********************************************************************
        # Given a curved segment will return a set of points that represent
        # straight line segments every "numDegrees" degrees
        #********************************************************************
        def GetPointsForApproxCurve(self, seg, numDegrees, isCircle=False):
            startAngle = self.GetCurveAngleAtPoint(seg, seg[0])

            FEQ = Blender4CNC.FloatsAreEqual
            
            (cX, cY) = seg[1][2:4]
            startV = (seg[0][0] - cX, seg[0][1] - cY) # seg[0] - center
            endV = (seg[1][0] - cX, seg[1][1] - cY) # seg[1] - center
            CW = self.GetCurveClockwiseness(seg)

            if isCircle:
                diff = 2 * pi
            else:
                diff = self.GetClockwiseAngleBetweenVectors(startV, endV)
                if not (seg[1][4] == 1): # not CW
                    diff = 2 * pi - diff

            stepRadians = pi * numDegrees / 180

            points = [(seg[0][0], seg[0][1])] # The start point Just 2d coords
            
            if diff < (stepRadians * 4):
                stepRadians = diff / 4
#                # Just add in a single segment
#                points.append((seg[1][0], seg[1][1])) # Just 2d coords
#                print(points)
#                return points

            # We must loop and add in a number of segments
            radius = self.GetArcRadius(seg)
            count = 1

            diff -= stepRadians
            while (diff > 0) and not FEQ(diff,0):
                nextAngle = startAngle - CW * stepRadians * count
                x = cos(nextAngle) * radius
                y = sin(nextAngle) * radius
                        
                nextPoint = (cX + x, cY + y) # center + (x,y)
                points.append(nextPoint)
                diff -= stepRadians
                count += 1
            # End while
            points.append((seg[1][0], seg[1][1])) #Just 2d coords
            return points

        #********************************************************************
        # Returns a Polytoxogon that has all curves approximated with 
        # straight lines every 10 degrees
        #********************************************************************
        def ApproximateCurves(self):
            
            pts = []
            for seg in self.lines:
                if len(seg[1]) == 2: # Segment is straight
                    pts.append((seg[0][0], seg[0][1]))
                else:
                    points = self.GetPointsForApproxCurve(seg, 10, False)
                    pts += points[:-1]
            
            return Blender4CNC.Polytoxogon(pts)
        
        #********************************************************************
        # Given two overlapping lines - returns the region of overlap
        #********************************************************************
        def GetOverlap(self, A, B):
            (a1, a2) = A
            (b1, b2) = B
            if self.PointIsOnSegment(A, b1) and self.PointIsOnSegment(A, b2):
                return (b1, b2)
            elif self.PointIsOnSegment(B, a1) and self.PointIsOnSegment(B, a2):
                return (a1, a2)
            elif self.PointIsOnSegment(A, b1) and self.PointIsOnSegment(B, a1):
                return (b1, a1)
            elif self.PointIsOnSegment(A, b1) and self.PointIsOnSegment(B, a2):
                return (b1, a2)
            elif self.PointIsOnSegment(A, b2) and self.PointIsOnSegment(B, a1):
                return (a1, b2)
            else:
                return (a2, b2)
                
        #********************************************************************
        # Get all intersections between all lines
        # Create a dictionary (keyed on line number) where each entry
        # contains a list of intersections with other lines
        #********************************************************************
        def GetIntersectionsBetweenAllLines(self, newLines):
            linesAndInts = {}
            for i,newLineI in enumerate(newLines):
                allInts = []
                for j,newLineJ in enumerate(newLines):
                    # Don't test a line against itself!
                    if i == j:
                        continue
                    ints = self.GetAllIntersections(newLineI, newLineJ)
                    if ints == inf:
                        # We have two overlapping line segments
                        # Find the start and end of the overlap
                        ints = self.GetOverlap(newLines[i], newLines[j])
                        ints = [(inf, ints)]
                    if isinstance(ints, list) and (len(ints) > 0):
                        # Tag each intersection with the number of the line we are on
                        allInts += [(j,x) for x in ints]
                #End for j
                linesAndInts[i] = allInts
            return linesAndInts
        
        #********************************************************************
        # linesAndInts is a dictionary containing lists of intersections
        # Remove any lines that only have one intersection (like an acute angle
        # squeezed them out)
        # Remove any lines that might intersect with multiple lines, BUT at
        # only one same point (like curves coming off from the same point)
        #
        # Here, 2 has two intersections with 3 and 4 but at the SAME point
        # (same for 7)
        #      
        #     *   
        #     | _3
        #    2|/ \ 
        #     *   *
        #    7|\_/
        #     |  4
        #     *
        #********************************************************************
        def RemoveLinesWithOnlyOneInt(self, linesAndInts):
            
            FEQ = Blender4CNC.FloatsAreEqual
            l = list(range(0,len(linesAndInts.keys())))
            while len(l) > 0:
                i = l.pop(0)
                ints = linesAndInts[i]
                if len(ints) == 1:
                    # Be careful - do not remove lines that have one "infinite" intersection
                    # because this will actually become two 
                    if ints[0][1][0] != inf:
                        otherLine = ints[0][0]
                        intersection = ints[0][1]
                        (x,y) = intersection
                        # Set this line to have no intersections
                        linesAndInts[i] = []
                        # Find the other line intersection and remove it
                        otherLineInts = linesAndInts[otherLine]
                        for j in range(0,len(otherLineInts)):
                            curIntersection = otherLineInts[j][1]
                            (x2,y2) = curIntersection
                            otherLineNum = otherLineInts[j][0]
                            if otherLineNum == i:
                                if curIntersection == intersection: # Exact equal should work in this case 
                                    otherLineInts.pop(j)
                                    l.append(otherLine)
                                    break
                        linesAndInts[otherLine] = otherLineInts
            #End for i, removing lines with one intersection

        #********************************************************************
        # Returns True if all lists in a dictionary are empty
        # l is a dictionary where the value for each key is a list
        #********************************************************************
        def AllListsAreEmpty(self, l):
            l2 = [len(l[x]) for x in l.keys()]
            return sum(l2) == 0
        
        def GetUniqueVerticesFromLines(self, newLines):
            FEQ = Blender4CNC.FloatsAreEqual
            vertices = []
            for line in newLines:
                for point in line:
                    # Is this point in the list of vertices?
                    found = False
                    for v in vertices:
                        if FEQ(point[0], v[0]) and FEQ(point[1], v[1]):
                            found = True
                            break
                    if not found:
                        vertices.append(point)
            return vertices
        def ShrinkExpandAndSplit(self, dist, CW_CCW, infiniteLoopCount=1000, avoidStartLines=[]):

            if Blender4CNC.FloatsAreEqual(0, dist):
                return [copy.copy(self)]

            if len(self.points) == 0:
                str2 = "ERROR - Cannot shrink/expand poly by " + str(dist) + ".\nTrying to shrink a poly that is too thin?\nOr using a too large cutter?"
                raise Blender4CNC.PolyException(str2, (0,0))
            
            lines = self.RemoveSuperfluousColinearPoints()

            # Get the lines that are parallel to the sides 
            # Check for circles in the list of points - they can mess up getting parallel lines
            points = self.points
            pList = self.points + [self.points[0]]
            FEQ = Blender4CNC.FloatsAreEqual
            nList = [i for i in range(0,len(pList)-1) if not self.PointIsStraight(pList[i+1])]
            nList = [i for i in nList if FEQ(pList[i][0], pList[i+1][0]) and FEQ(pList[i][1], pList[i+1][1])]
            polyList = [Blender4CNC.Polytoxogon([(pList[i][0], pList[i][1]), pList[i+1]]) for i in nList]
            if (len(nList) > 0):
                points2 = []
                for i in range(0,len(points)):
                    points2.append(pList[i])
                    if i in nList:
                        # The Polytoxogon constructor will safely split the circle as long as we pass in a simple start point
                        ndx = nList.index(i)
                        points2.append(polyList[ndx].points[1])
                tempPoly = Blender4CNC.Polytoxogon(points2)
                newLines = tempPoly.GetParallelSides(dist)
            else:
                # Get the lines that are parallel to the sides 
                newLines = self.GetParallelSides(dist)

            linesAndInts = self.GetIntersectionsBetweenAllLines(newLines)

            # At this point, linesAndInts contains all lines and for each line, a list
            # of intersections with other lines
            
            # If all lists are empty - maybe we are trying to shrink a poly that is very (too) thin
            if self.AllListsAreEmpty(linesAndInts):
                str2 = "ERROR - Cannot shrink/expand poly by " + str(dist) + ".\nTrying to shrink a poly that is too thin?\nOr using a too large cutter?"
                raise Blender4CNC.PolyException(str2, (self.points[0][0],self.points[0][1]))
            
            # Remove "stub" lines that have been cut off
            self.RemoveLinesWithOnlyOneInt(linesAndInts)

            # We may have some infinite overlaps in the lines and intersections
            for k in linesAndInts.keys():
                l = linesAndInts[k]
                l2 = []
                for item in l:
                    if item[1][0] == inf:
                        l2.append((item[0], item[1][1][0])) 
                        l2.append((item[0], item[1][1][1])) 
                    else:
                        l2.append(item) 
                linesAndInts[k] = l2
            
            # Create a list of new lines from dictionary
            origNewLines = newLines
            newLines = []
            for k in linesAndInts.keys():
                l = linesAndInts[k]
                l2 = [x[1] for x in l]
                #print("origNewLines[k]=", origNewLines[k])
                #print("l2=", l2)
                newList = self.OrderIntersections(origNewLines[k], l2)
                #print("newList=", newList)
                if len(origNewLines[k][1]) == 5:
                    (a,b,c,d,e) = origNewLines[k][1]
                    newList2 = []
                    for p in newList:
                        p = (p[0], p[1], c,d,e)
                        newList2.append(p)
                    newList = newList2
                #print("newList (again)=", newList)
                i = 0
                while i < (len(newList)-1):
                    newLines.append((newList[i], newList[i+1]))
                    i += 1
                

            # Remove any lines that have zero length
            newLines = self.RemoveZeroLengthLines(newLines)

            if len(newLines) <= 1:
                str2 = "ERROR - Cannot shrink/expand poly by " + str(dist) + ". Are some points too close?\nTry moving some points slightly."
                raise Blender4CNC.PolyException(str2, (self.points[0][0],self.points[0][1]))

            # Get a set of vertices (be wary of tolerance)
            vertices = self.GetUniqueVerticesFromLines(newLines)
            # Point lines to vertices
            vLines = []
            for line in newLines:
                vs = [i for i,v in enumerate(vertices) if FEQ(line[0][0], v[0]) and FEQ(line[0][1], v[1])]
                vs2 = [i for i,v in enumerate(vertices) if FEQ(line[1][0], v[0]) and FEQ(line[1][1], v[1])]
                vLines.append(vs + vs2)
            origVLines = copy.copy(vLines)
            # Create "out" vectors
            outVectors = [self.GetSegVectorAtPoint(line, line[0]) for line in newLines]
            # Create "in" vectors
            inVectors = [self.GetSegVectorAtPoint(line, line[1]) for line in newLines]
            inVectors = [(-x[0], -x[1], -x[2]) for x in inVectors]
            
            # Start at segment 0
            curSeg = 0
            segs = [0]
            polys = []
            loopCount = 0
            while True:
                loopCount += 1
                if loopCount > infiniteLoopCount:
                    raise Blender4CNC.PolyException("ShrinkExpandAndSplit appears to be stuck in infinite loop?", (self.points[0][0],self.points[0][1]))
                # Find where curSeg goes next
                # Get current end point
                curEndNdx = vLines[curSeg][1]
                # Get all segments that start from this point
                nextLines = [idx for idx, value in enumerate(vLines) if value[0] == curEndNdx]
                if len(nextLines) == 0:
                    # We have found a non-loop chain, trigger the ending
                    segs.append(segs[0])
                else:
                    # Get the "right-most" vector
                    nextSeg = nextLines[0]
                    for i in range(0,len(nextLines)-1):
                        segB = nextLines[i+1]
                        diff = self.CompareSegVectorAngle(inVectors[curSeg], outVectors[nextSeg], outVectors[segB])
                        if diff <= 0:
                            nextSeg = segB
                    segs.append(nextSeg)
                curSeg = segs[-1]
                # Check if we just came back to the start OR if we looped around inside the chain...
                if curSeg in segs[:-1]:
                    # Remove the duplicated segment
                    segs.pop(-1)
                    # And remove anything up to the curSeg
                    startNdx = segs.index(curSeg)
                    segs = segs[startNdx:]
                    if len(nextLines) > 0:
                        polys.append(segs)
                    # "Remove" these segments from the main list
                    for ndx in segs:
                        vLines[ndx] = [-1,-1]
                    # Find any other segment to follow
                    moreSegs = [(vLine[0] != -1) for vLine in vLines]
                    if True not in moreSegs:
                        break
                    curSeg = moreSegs.index(True)
                    segs = [curSeg]
            
            # Convert to actual polytoxogons
            polys2 = []
            for poly in polys:
                polys2.append(Blender4CNC.Polytoxogon([newLines[ndx][1] for ndx in poly]))
                
            # It is possible that we have some infinite overlap loops of no area
            # Some of these may be valid and should be connected to a poly loop that has area
            # Some of these may have invalid loops that touch the original poly
            
            # Let's start by removing line segments from polys where those segments touch the original poly
            haveOverlapLines = False
            for i,poly in enumerate(polys2):
#                (poly1IsSame, poly1IsInside, poly1Touches, poly1IsOutside) = self.SameInsideOutside(poly)
                linesAndIntsPoly = self.GetIntersectionsBetweenAllLines(poly.lines)
                overlapLines = []
                for k in linesAndIntsPoly.keys():
                    l = [k for x in linesAndIntsPoly[k] if x[1][0] == inf]
                    overlapLines += l
                if len(overlapLines) > 0:
                    haveOverlapLines = True
                    # We have overlap lines - do any of them touch the original poly?
                    segmentsThatTouch = []
                    for ndx in overlapLines:
                        lineA = poly.lines[ndx]
                        for lineB in self.lines:
                            ints = self.GetAllIntersections(lineA, lineB)
                            if len(ints) > 0:
                                segmentsThatTouch.append(ndx)
                    if len(segmentsThatTouch) > 0:
                        # This poly needs to have some segments removed
                        segmentsThatTouch = list(set(segmentsThatTouch))
                        segmentsThatTouch.sort()
                        segmentsThatTouch.reverse()
                        for ndx in segmentsThatTouch:
                            poly.lines.pop(ndx)
                        points = [x[1] for x in poly.lines]
                        points = [points[-1]] + points[:-1]
                        polys2[i] = Blender4CNC.Polytoxogon(points)
                
            return polys2

        #********************************************************************
        # This ASSUMES the lines are straight!
        # Returns true if the two line segments overlap at all.
        # If two line segments just touch at a common point, this is not
        # counted as overlap.
        #********************************************************************
        def LineSegmentsOverlap(self, A, B, depth=0):
            # Check if they are exact overlap
            A0 = A[0]
            A1 = A[1]
            B0 = B[0]
            B1 = B[1]
            if (self.PointsAreEqual(A0, B0) and self.PointsAreEqual(A1, B1)):
                return True
            if (self.PointsAreEqual(A0, B1) and self.PointsAreEqual(A1, B0)):
                return True

            lineEquation = self.GetLineEquation(A)
            if self.PointIsOnInfiniteLine(A, B0[0], B0[1], lineEquation) and self.PointIsOnInfiniteLine(A, B1[0], B1[1], lineEquation):
                if self.PointIsOnAndWithinLineSegment(A, B0[0], B0[1]):
                    return True
                if self.PointIsOnAndWithinLineSegment(A, B1[0], B1[1]):
                    return True
                if self.PointIsOnAndWithinLineSegment(B, A0[0], A0[1]):
                     return True
                if self.PointIsOnAndWithinLineSegment(B, A1[0], A1[1]):
                     return True
            return False

        #********************************************************************
        # Returns True if the point is on the line (infinite line NOT just
        # the segment)
        #********************************************************************
        def PointIsOnInfiniteLine(self, line, px, py, lineEquation):

            FEQ = Blender4CNC.FloatsAreEqual
            # Check for vertical line
            if FEQ(line[0][0],line[1][0]):
                return FEQ(line[0][0], px)
                
            (m,C) = lineEquation
            y = m * px + C
            return FEQ(y, py)

        #********************************************************************
        # Returns true if the segment exactly appears in poly2
        # (In either direction)
        #********************************************************************
        def IsSegmentInPoly(self, line, poly2):

            p1 = line[0]
            p1x = p1[0]
            p1y = p1[1]
            p2 = line[1]
            p2x = p2[0]
            p2y = p2[1]
            FEQ = Blender4CNC.FloatsAreEqual
            if len(line[1]) == 2: # Segment is straight
                for line2 in poly2.lines:
                    if len(line2[1]) == 2: # Segment is straight
                        q1 = line2[0]
                        q2 = line2[1]

                        # ((p1 == q1) and (p2 == q2)) or ((p1 == q2) and (p2 == q1)):
                        if FEQ(p1x, q1[0]) and FEQ(p1y, q1[1]) and FEQ(p2x, q2[0]) and FEQ(p2y, q2[1]):
                            return True
                        if FEQ(p1x, q2[0]) and FEQ(p1y, q2[1]) and FEQ(p2x, q1[0]) and FEQ(p2y, q1[1]):
                            return True
            else:
                pC = line[1][2:4]
                pC = pC
                pCW = line[1][4]
                for line2 in poly2.lines:
                    if not len(line2[1]) == 2: # not Segment is straight
                        q1 = line2[0]
                        q2 = line2[1]
                        qC = line2[1][2:4]
                        qC = qC
                        qCW = line2[1][4]
                        # pC == qC:
                        if FEQ(pC[0], qC[0]) and FEQ(pC[1], qC[1]):
                            # ((p1 == q1) and (p2 == q2) and (pCW == qCW)):
                            if (pCW == qCW):
                                if FEQ(p1x, q1[0]) and FEQ(p1y, q1[1]) and FEQ(p2x, q2[0]) and FEQ(p2y, q2[1]):
                                    return True
                            else:
                                # ((p1 == q2) and (p2 == q1) and (pCW != qCW)):
                                if FEQ(p1x, q2[0]) and FEQ(p1y, q2[1]) and FEQ(p2x, q1[0]) and FEQ(p2y, q1[1]):
                                    return True
            return False

        #********************************************************************
        # Returns true if the point is on the line segment (straight or curved)
        # the endpoints are NOT inclusive
        #********************************************************************
        def PointIsOnAndWithinSegment(self, lineIn, pt):
            if len(lineIn[1]) == 2: # Segment is straight
                return self.PointIsOnAndWithinLineSegment((lineIn[0], lineIn[1]), pt[0], pt[1])
            else:
                # Curve
                B = lineIn
                angA = self.GetCurveAngleAtPoint(B, B[0])
                angB = self.GetCurveAngleAtPoint(B, B[1])
                ang = self.GetCurveAngleAtPoint(B, pt)
                
                FEQ = Blender4CNC.FloatsAreEqual
                if FEQ(ang, angA):
                    return False
                if FEQ(ang, angB):
                    return False
                return self.IsPointOnCurve(B, pt)
                
        #********************************************************************
        # Returns true if the point falls on the segment (the end points are
        # NOT inclusive)
        # The given line MUST be a straight segment
        #********************************************************************
        def PointIsOnAndWithinLineSegment(self, lineIn, px, py):
            return self.PointIsOnStraightSegmentSub(lineIn, px, py, False)

        #********************************************************************
        # Return true if the point is on the segment
        #********************************************************************
        def PointIsOnSegment(self, line, pt):
                
            if len(line[1])==2: # Straight Segment
                return self.PointIsOnStraightSegment(line, pt)
            else:
                return self.IsPointOnCurve(line, pt)

        #********************************************************************
        # Returns true if the point falls on the segment (includes the end points)
        # The given line MUST be a straight segment
        #********************************************************************
        def PointIsOnStraightSegment(self, lineIn, pt):
            return self.PointIsOnStraightSegmentSub(lineIn, pt[0], pt[1], True)
            
        #********************************************************************
        # if tf == True Returns true if the point falls on the segment (inclusive
        # of the end points)
        # if tf == False Returns true if the point falls on the line of the 
        # segment BUT is NOT on the actual segment (exclusive of the end points)
        # The given line MUST be a straight segment
        #********************************************************************
        def PointIsOnStraightSegmentSub(self, lineIn, px, py, tf):
                
            line = lineIn

            # Check if the line is a single point
            if Blender4CNC.FloatsAreEqual(line[0][0],line[1][0]):
                if Blender4CNC.FloatsAreEqual(line[0][1], line[1][1]):
                    return False
                # Flip to horizontal
                line = self.RotateSegment90Degrees((line[0], line[1]))
                line = [line[0], line[1]]
                (px,py) = self.RotatePoint90Degrees((px,py))
            line0x = line[0][0]
            line1x = line[1][0]


            # GetLineEquation
            # The 1st line A, y = mx + C
            # m = dy / dx
            a0y = line[0][1]
                
            m = (line[1][1] - a0y) / (line1x - line0x)
            # C = y - mx
            C = a0y - m * line0x

            y = m * px + C
            if not Blender4CNC.FloatsAreEqual(y, py):
                return False
            
            # It is on the line, check if on the segment
            x1 = min(line0x, line1x)
            x2 = max(line0x, line1x)
                
            if Blender4CNC.FloatsAreEqual(px, line0x):
                return tf
            
            if Blender4CNC.FloatsAreEqual(px, line1x):
                return tf

            return ((px > x1) and (px < x2))

        #********************************************************************
        # Converts a vector into a nice printable string
        #********************************************************************
        def GetVectorAsString(self, v):
            s = str(v)
            return s

        #********************************************************************
        # Returns a normalized vector of a straight line
        # The line MUST be straight NOT curved
        #********************************************************************
        def GetNormalizedVectorOfLine(self, line1):
            p1 = line1[0]
            p2 = line1[1]
            # p2 - p1
            x = p2[0] - p1[0]
            y = p2[1] - p1[1]
            m = sqrt(x**2 + y**2) # Length
            v = (x/m, y/m) # Normalize
            return v
            
        #********************************************************************
        # Returns a point that is the middle of the segment
        # Handles straight lines, curves, circles
        #********************************************************************
        def GetMidOfSegment(self, line):

            (p1, p2) = line
            p1 = p1
            p2 = p2
            if len(line[1]) == 2: # Segment is straight
                x = p1[0] + (p2[0] - p1[0])/2
                y = p1[1] + (p2[1] - p1[1])/2 
                return (x,y)

            # Be careful of a circle - the midpoint is halfway around the circle!
            (cX, cY) = line[1][2:4]
            v1 = (p1[0] - cX, p1[1] - cY) # p1 - center
            v2 = (p2[0] - cX, p2[1] - cY) # p2 - center
            # Check for circle
            # (v1 == v2):
            if Blender4CNC.FloatsAreEqual(v1[0], v2[0]) and Blender4CNC.FloatsAreEqual(v1[1], v2[1]):
                v1 = (cX - v1[0], cY - v1[1]) # center - v1
                return v1

            if not self.SegmentIsClockwise((line[0], line[1])):
                (v1, v2) = (v2, v1)
            
            diffAngle = self.GetClockwiseAngleBetweenVectors(v1,v2) / 2
            
            v1 = self.GoClockwiseAngleVector(v1, diffAngle)

            AA = (v1[0] + cX, v1[1] + cY) # v1 + center
            return AA

        #********************************************************************
        # Return True if the list of points represent a circle
        #********************************************************************
        def PointsRepresentCircle(self, p):
            # Check for circle
            if len(p) == 2:
                if self.PointsAreEqual(p[0], p[1]):
                    if (len(p[0]) == 2) and (len(p[1]) == 5):
                        return True
                    if (len(p[0]) == 5) and (len(p[1]) == 2):
                        return True
            return False

        #********************************************************************
        # Given a list of points, returns a list of segments between each
        # consecutive point
        #********************************************************************
        def GetListOfLinesFromPoints(self, p):
            # Check for circle
            points2 = [x for x in p]
            if self.PointsRepresentCircle(points2):
                # This is a circle just leave it as one line
                # Make sure the curve point is second
                if len(p[0]) == 5:
                    return [(p[1], p[0])]
                else:
                    return [(p[0], p[1])]

            if len(p) == 0:
                return []
            l = []
            for i in range(0,len(p)-1):
                l += [(p[i], p[i+1])]
            l += [(p[-1], p[0])]
            l = [(x[0], x[1]) for x in l]
            return l

        #********************************************************************
        # All functions that call this SHOULD be checking for a vertical
        # line first, however if they don't, this function will return
        # a tuple containing a single value k for the formula:
        #   x = k
        # otherwise, returns a tuple of m,C for the typical formula:
        #   y = mx + C
        #********************************************************************
        def GetLineEquation(self, A):
            # The 1st line A, y = mx + C
            # m = dy / dx
            a0x = A[0][0]
            a1x = A[1][0]
            a0y = A[0][1]
                
            if Blender4CNC.FloatsAreEqual(a1x, a0x):
                # Vertical line
                return (a0x)
            
            # Non-vertical line
            m = (A[1][1] - a0y) / (a1x - a0x)
            # C = y - mx
            C = a0y - m * a0x
            return (m,C)

        #********************************************************************
        # Convert a line to a nice printable string
        #********************************************************************
        def GetLineAsString(self, line):
            s = self.GetVectorAsString(line[0])
            s += " to "
            s += self.GetVectorAsString(line[1])
            return s
        
        #********************************************************************
        # Return an angle that is "angle" more counter-clockwise than "start"
        # Return angle is between -pi and pi
        # (start - angle in a clockwise direction)
        # Angles are in radians
        #********************************************************************
        def GoCounterClockwiseAngle(self, start, angle):
            return self.ClipAnglePlusMinusPi(start + angle)

        #********************************************************************
        # Return an angle that is "angle" more clockwise than "start"
        # Return angle is between -pi and pi
        # (start + angle in a clockwise direction)
        # Angles are in radians
        #********************************************************************
        def GoClockwiseAngle(self, start, angle):
            return self.ClipAnglePlusMinusPi(start - angle)


        #********************************************************************
        # Given new set of lines, recreates the poly lines and points
        #********************************************************************
        def RecreatePolyFromLines3(self, newLines):
            self.lines = newLines
            self.points = [x[1] for x in self.lines]
            self.points = [self.points[-1]] + self.points[0:-1]
        #********************************************************************
        # Converts circles to two curves
        #********************************************************************
        def BreakupCircles3(self):
            FEQ = Blender4CNC.FloatsAreEqual
            # Find any circles
            newLines = []
            for line in self.lines:
                (a,b) = line
                lineA = None
                if (len(b) > 2) and FEQ(a[0], b[0]) and FEQ(a[1], b[1]):
                    # We have a circle
                    (cX, cY, CW) = b[2:5]
                    x = cX - (a[0] - cX)
                    y = cY - (a[1] - cY)
                    newP2 = (x, y, cX, cY, CW)
                    newLines.append((line[0], newP2))
                    newLines.append((newP2, line[1]))
                else:
                    newLines.append(line)
            if len(self.lines) != len(newLines):
                self.RecreatePolyFromLines3(newLines)
        #********************************************************************
        def RemoveZeroLengthLines3(self):
            newLines = self.RemoveZeroLengthLines(self.lines)
            if len(self.lines) != len(newLines):
                self.RecreatePolyFromLines3(newLines)
        #********************************************************************
        # Return a list of lines where zero length lines have been removed
        #********************************************************************
        def RemoveZeroLengthLines(self, newLines):
            return [line for line in newLines if not self.PointsAreEqual(line[0], line[1])]
        #********************************************************************
        # Removes superfluous points (straight lines)
        #********************************************************************
        def RemoveSuperfluousStraight(self):
            changed = True
            while changed:
                changed = self.RemoveSuperfluousStraightSub()
        #********************************************************************
        # Removes superfluous points (straight lines) subroutine
        #********************************************************************
        def RemoveSuperfluousStraightSub(self):
            newLines = []
            i = 0
            while i < (len(self.lines)):
                lineA = self.lines[i]
                if i != (len(self.lines)-1):
                    lineB = self.lines[i+1]
                else:
                    lineB = self.lines[0]
                (a,b) = lineA
                (c,d) = lineB
                newLine = None
                if (len(b) == 2) and (len(d) == 2): 
                    # Segment is straight
                    v1 = self.GetNormalizedVectorOfLine(lineA)
                    v2 = self.GetNormalizedVectorOfLine(lineB)
                    if self.PointsAreEqual(v1, v2):
                        # Co-linear lines - eliminate 2nd line
                        newLine = (lineA[0], lineB[1])
                        newLines.append(newLine)
                        i += 1
                if newLine == None:                
                    newLines.append(lineA)
                i += 1
            changed = len(self.lines) != len(newLines)
            # It is possible that a glitch occurs at the very beginning of the sequence and a line segment
            # gets added prematurely becuase it is the "2nd" part of a pair involved with a superfluous point
            if not changed:
                p = newLines[-1][1]
                a = newLines[0][0]
                b = newLines[0][1]
                p = p[0:2]
                a = a[0:2]
                b = b[0:2]
                if (not self.PointsAreEqual(p, a)) and self.PointsAreEqual(p, b):
                    newLines.pop(0)
                    changed = True
            if changed:
                self.RecreatePolyFromLines3(newLines)
            return changed
        #********************************************************************
        # Removes superfluous points (curves)
        #********************************************************************
        def RemoveSuperfluousCurve(self):
            changed = True
            while changed:
                changed = self.RemoveSuperfluousCurveSub()
        #********************************************************************
        # Removes superfluous points (curves) subroutine
        #********************************************************************
        def RemoveSuperfluousCurveSub(self):
            newLines = []
            i = 0
            while i < (len(self.lines)):
                lineA = self.lines[i]
                if i != (len(self.lines)-1):
                    lineB = self.lines[i+1]
                else:
                    lineB = self.lines[0]
                (a,b) = lineA
                (c,d) = lineB
                newLine = None
                if (len(b) == 5) and (len(d) == 5): 
                    # We have two curves
                    center1 = b[2:4]
                    center2 = d[2:4]
                    radius1 = self.GetArcRadius(lineA)
                    radius2 = self.GetArcRadius(lineB)
                    dir1 = b[4]
                    dir2 = d[4]
                    if self.PointsAreEqual(center1, center2) and Blender4CNC.FloatsAreEqual(radius1, radius2) and (dir1 == dir2):
                        # "Co-linear" curves 
                        # We have to check that 
                        # (a) the total curve goes from a to b/c to d
                        # (b) the sum of these two curves would not exceed 180 degrees
                        va = (a[0] - center1[0], a[1] - center1[1])
                        vbc = (b[0] - center1[0], b[1] - center1[1])
                        vd = (d[0] - center1[0], d[1] - center1[1])
                        a_bc = self.GetClockwiseAngleBetweenVectors(va, vbc)
                        a_d = self.GetClockwiseAngleBetweenVectors(va, vd)
                        bc_d = self.GetClockwiseAngleBetweenVectors(vbc, vd)
                        if (dir1 == 1) and (a_bc <= a_d):
                            # Clockwise
                            # The curve goes from a to b/c to d
                            if a_d <= math.pi:
                                # We can eliminate this "co-linear" point on the curve
                                newLine = (lineA[0], lineB[1])
                                newLines.append(newLine)
                                i += 1
                        if (dir1 == -1) and (a_bc >= a_d):
                            # Counter-Clockwise
                            # The curve goes from a to b/c to d
                            a_d = math.pi * 2 - a_d
                            if a_d <= math.pi:
                                # We can eliminate this "co-linear" point on the curve
                                newLine = (lineA[0], lineB[1])
                                newLines.append(newLine)
                                i += 1
                if newLine == None:
                    newLines.append(lineA)
                i += 1
            changed = len(self.lines) != len(newLines)
            if changed:
                self.RecreatePolyFromLines3(newLines)
            return changed
        #********************************************************************
        # Converts circles to two curves
        # Filters out lines of zero length 
        # Removes superfluous points
        # Cuts curves larger than 180 degrees into two curves
        #********************************************************************
        def CleanUpPoly_UI(self):
            FEQ = Blender4CNC.FloatsAreEqual

            # Converts circles to two curves
            self.BreakupCircles3()

            # Filter out lines of zero length (can only occur on straight lines
            # since we have just converted all circles to 2 semi-circles)
            self.RemoveZeroLengthLines3()

            # Remove Superfluous points 
            self.RemoveSuperfluousStraight()
            self.RemoveSuperfluousCurve()

            # Any curve that is larger than 180 degrees must be split in half
            poly = self.SplitUpLargeCurves()
            if poly != self:
                self.points = poly.points
                self.lines = poly.lines
           
        #********************************************************************
        # Convert a point into a text readable form
        #********************************************************************
        def ConvertPointToString(self, pt):
            str = "(%3.4f,%3.4f)" % (pt[0], pt[1])
            return str

        #********************************************************************
        # Returns true if the points are equal within a tiny error amount
        #********************************************************************
        def PointsAreEqual(self, pt1, pt2):
            return (Blender4CNC.FloatsAreEqual(pt1[0], pt2[0]) and Blender4CNC.FloatsAreEqual(pt1[1], pt2[1]))

        #********************************************************************
        # Rotate a vector counterclockwise by given number of radians
        # Returns the new vector
        #********************************************************************
        def RotateVector(self, p, radians):
            s = sin(radians)
            c = cos(radians)
            xnew = p[0] * c - p[1] * s
            ynew = p[0] * s + p[1] * c
            if Blender4CNC.FloatsAreEqual(xnew, 0):
                xnew = 0
            if Blender4CNC.FloatsAreEqual(ynew, 0):
                ynew = 0
            return (xnew, ynew)

        #********************************************************************
        # Returns true if the line is part of a circle where the first
        # point is a "curve" point and the 2nd point is a "straight" 2d point
        # and there is zero length between them.
        #********************************************************************
        def ZeroLengthCircularLine(self, line):
            (p1, p2) = line
            if (len(p1) > 2) and (len(p2) == 2):
                return self.PointsAreEqual(p1, p2)
            return False

        #********************************************************************
        # Return true if the segment is clockwise
        #********************************************************************
        def SegmentIsClockwise(self, line):
            if len(line[1]) > 2:
                return (line[1][4] == 1)
            return False

        #********************************************************************
        # Return a "curved" 3d vector of the segment at the 
        # given point - the x,y components are "normalized" before we add the
        # z component
        # Straight segments have z = 0
        # Curved segments have +/-(1/r) = z
        #********************************************************************
        def GetSegVectorAtPoint(self, seg, pt):

            p1 = seg[0]
            p2 = seg[1]
            if self.PointIsStraight(seg[1]): # A straight line
                x = p2[0] - p1[0] # p2 - p1
                y = p2[1] - p1[1] 
                z = 0
            else:
                # A curve, get tangent to circle at this point
                centerX = p2[2]
                centerY = p2[3]
                
                # To minimize floating point errors, get radius twice, using both points of arc and average
                x = p2[0] - centerX
                y = p2[1] - centerY
                r1 = math.sqrt(x**2 + y**2)
                
                x = p1[0] - centerX
                y = p1[1] - centerY
                r2 = math.sqrt(x**2 + y**2)
                radius = (r1 + r2) / 2
                CW = p2[4]
                z = -CW/radius

                (x,y) = self.GetTangentOnCircleAtPoint((centerX, centerY), pt, CW)
            m = sqrt(x**2 + y**2) # Length
            x = x/m # Normalize
            y = y/m
            return (x, y, z)

        #********************************************************************
        # Determines if v3 is fully inside the vectors v1 clockwise to v2
        # Note these can be curved vectors! Eg. if v3 lies exactly on v1 
        # but v3 is a wider curve than v1, then v3 is NOT inside 
        #********************************************************************
        def IsSegVectorInside(self, v3, v1, v2):
            a1_2 = self.GetClockwiseAngleBetweenVectors(v1, v2)
            a1_3 = self.GetClockwiseAngleBetweenVectors(v1, v3)
            a3_2 = self.GetClockwiseAngleBetweenVectors(v3, v2)

            # Check if the simple angles overlap
            if (a1_3 == 0): # 3 lies on 1
                return v3[2] < v1[2] # curves to right

            # Check if the simple angles overlap
            if (a3_2 == 0): # 3 lies on 2
                return v3[2] > v2[2] # curves to left

            # Simple angles do not overlap
            return (a1_3 < a1_2)

        #********************************************************************
        # Compares the angle vStart-v1 with vStart-v2
        # returns -1,0,+1 if <,=,>
        #********************************************************************
        def CompareSegVectorAngle(self, vStart, v1, v2):
            a1_2 = self.GetClockwiseAngleBetweenVectors(vStart, v1)
            a1_3 = self.GetClockwiseAngleBetweenVectors(vStart, v2)
                
            # [(0.0, 1.0, -2.0), (-0.0, -1.0, 2.0), (0.0, 1.0, 2.0)]                
            # If an angle comes to 0 - is it really zero? (see above example where vStart is curving in from
            # the "left" and v2 is curving in from the "right" - the GetClockwiseAngleBetweenVectors function
            # will return 0 for a1_3 but it should be 2*PI ?
            if Blender4CNC.FloatsAreEqual(a1_2, 0):
                if (vStart[2] < v1[2]):
                    # vStart.z could be -1, or 0 if v1.z is 1
                    # vStart.z could be -1 if v1.z is 0 or 1
                    a1_2 = math.pi * 2
            if Blender4CNC.FloatsAreEqual(a1_3, 0):
                if (vStart[2] < v2[2]):
                    # vStart.z could be -1, or 0 if v2.z is 1
                    # vStart.z could be -1 if v2.z is 0 or 1
                    a1_3 = math.pi * 2

            # Check if simple angles overlap
            if Blender4CNC.FloatsAreEqual(a1_2, a1_3):
                # Must check z component
                if Blender4CNC.FloatsAreEqual(v1[2], v2[2]):
                    return 0
                elif v2[2] < v1[2]: # curves to right
                    return -1 # less than
                else:
                    return 1
            else:
                if a1_2 < a1_3:
                    return -1
                else:
                    return 1
                
        #********************************************************************
        # return poly - poly2 (subtract poly2 from poly)
        #********************************************************************
        def IsSegmentFullyOutsidePoly(self, seg):                        
            (p1, p2) = seg
            startsOnBoundary = self.IsPointOnBoundary(p1)
            endsOnBoundary = self.IsPointOnBoundary(p2)
            if startsOnBoundary:
                if endsOnBoundary:
#                    midPt = self.GetMidOfSegment((seg[0], seg[1]))
                    midPt = self.GetMidOfSegment(seg)
                    midOnBoundary = self.IsPointOnBoundary(midPt)
                    return (not midOnBoundary and not self.IsPointInside(midPt))
                else:
                    endsInside = self.IsPointInside(p2)
                    return not endsInside
            startsInside = self.IsPointInside(p1)
            
            if endsOnBoundary:
                return not startsInside
            elif not startsInside:
                return True
            # This can never happen
            #elif endsInside:
            #    return True
            else:
                return False

        def IsSegmentFullyInsidePoly(self, seg):                        

            (p1, p2) = seg
            startsOnBoundary = self.IsPointOnBoundary(p1)
            endsOnBoundary = self.IsPointOnBoundary(p2)

            if startsOnBoundary:
                if endsOnBoundary:
#                    midPt = self.GetMidOfSegment((seg[0], seg[1]))
                    midPt = self.GetMidOfSegment(seg)
                    midOnBoundary = self.IsPointOnBoundary(midPt)
                    return (not midOnBoundary and self.IsPointInside(midPt))
                else:
                    endsInside = self.IsPointInside(p2)
                    return endsInside

            startsInside = self.IsPointInside(p1)
                
            if endsOnBoundary:
                return startsInside
            elif startsInside:
                return True
            # This can never happen
            #elif endsInside:
            #    return True
            else:
                return False
        def RemoveSegmentsOnOutside(self, lines2):
            # Remove any lines on poly2 that are outside poly1
            num = 0
            while num < len(lines2):
                if self.IsSegmentFullyOutsidePoly(lines2[num]):
                    lines2.pop(num)
                else:
                    num += 1
                    
        def RemoveSegmentsOnInside(self, lines1):
            num = 0
            while num < len(lines1):
                if self.IsSegmentFullyInsidePoly(lines1[num]):
                    lines1.pop(num)
                else:
                    num += 1
        def RemoveSegmentsOnBoundary(self, lines1):
            num = 0
            while num < len(lines1):
                if self.IsSegmentInPoly(lines1[num], self):
                    lines1.pop(num)
                else:
                    num += 1
        def IsSegmentInListRemoveIt(self, line, poly2Lines):

            (p1, p2) = line
            FEQ = Blender4CNC.FloatsAreEqual
            if len(line[1]) == 2: # Segment is straight
                for line2 in poly2Lines:
                    if len(line2[1]) == 2: # Segment is straight
                        (q1, q2) = line2
                        if (self.PointsAreEqual(p1,q1) and self.PointsAreEqual(p2,q2)):
                            # Same direction
                            poly2Lines.remove(line2)
                            return (True, True)
                        if (self.PointsAreEqual(p1,q2) and self.PointsAreEqual(p2,q1)):
                            # Opposite direction
                            poly2Lines.remove(line2)
                            return (True, False)
            else:
                pC = line[1][2:4]
                pCW = line[1][4]
                p1 = p1
                p2 = p2
                for line2 in poly2Lines:
                    if not (len(line2[1]) == 2): # not Segment is straight
                        (q1, q2) = line2
                        qC = line2[1][2:4]
                        qCW = line2[1][4]
                        if pC == qC:
                            q1 = q1
                            q2 = q2
                            # p1 == q1 and p2 == q2
                            if FEQ(p1[0], q1[0]) and FEQ(p1[1], q1[1]) and FEQ(p2[0], q2[0]) and FEQ(p2[1], q2[1]) and (pCW == qCW):
                                # Same direction
                                poly2Lines.remove(line2)
                                return (True, True)
                            # p1 == q2 and p2 == q1
                            if FEQ(p1[0], q2[0]) and FEQ(p1[1], q2[1]) and FEQ(p2[0], q1[0]) and FEQ(p2[1], q1[1]) and (pCW != qCW):
                                # Opposite direction
                                poly2Lines.remove(line2)
                                return (True, False)
            return (False, False)
        def Subtract(self, poly2, infiniteLoopCounter = -1):
            poly3 = poly2.ReverseLineDirections()
            return self.Add(poly3)
                
        
        def FollowPathOfSegments(self, allLines, LR):
            polyList = []
            linesList = []
            while (len(allLines) > 0):
                # Now go around the poly and follow the left-most path
                (p1, p2) = allLines[0]
                points = [p2]
                linesList = [allLines[0]]
                oldLine = allLines[0]
                allLines.pop(0)
                pt = p2
                while (len(allLines) > 0):
                    l1 = [line for line in allLines if self.PointsAreEqual(pt, line[0]) == True]
                    if len(l1) > 1:
                        # Must choose left-most line
                        # Get the current segment vector and reverse it
                        curSegVec = self.GetSegVectorAtPoint((oldLine[0], oldLine[1]), oldLine[1])
                        curSegVec = (-curSegVec[0], -curSegVec[1], -curSegVec[2])

                        # Get the seg vectors for all lines that leave this point
                        listVectors = []
                        DRAMATIC_STOP_PT = oldLine[1]
                        for i in range(0, len(l1)):
                            # Ignore lines that are circular, going from curve point to 2d point
                            # and have zero length
                            line2 = l1[i]
                            if self.ZeroLengthCircularLine((line2[0], line2[1])):
                                # FAILS COVERAGE
                                DRAMATIC_STOP
                                continue

                            segVec = self.GetSegVectorAtPoint((line2[0], line2[1]), oldLine[1])
                            listVectors.append((segVec, i))
                            
                        # Now go through the list and find the "leftmost" line OR rightmost
                        smallNdx = 0
                        nextNdx = 1
                        watchOutFlag = False
                        while nextNdx < len(listVectors):
                            (smallSegVec, smallINum) = listVectors[smallNdx]
                            (nextSegVec, nextINum) = listVectors[nextNdx]
                            lessThan = self.CompareSegVectorAngle(curSegVec, smallSegVec, nextSegVec)
                            if LR == True:
                                LR_Value = -1
                            else:
                                LR_Value = 1
                            if lessThan == LR_Value:
                                # We are pointing at the smallest already!
                                pass 
                            elif lessThan == 0:
                                # This can occur with lines that are really tiny or really close
                                # Simple angles are equal
                                # v1[2], v2[2] =  -7.999999999993221 -8.000000000000014
                                # equal =  True
                                # We are going to try and assume we are pointing to the left most
                                # and hope that the networks connect reasonably
                                # FAILS COVERAGE
                                pass
                            else:
                                # The next seg is smaller!
                                smallNdx = nextNdx
                            nextNdx += 1
                        # End while loop
                        # After the loop, smallNdx points to the smallest (leftmost segment)
                        (smallSegVec, smallINum) = listVectors[smallNdx]
                        
                        line = l1[smallINum]
                        (p1, p2) = line
                        oldLine = line
                        points += [p2]
                        allLines.remove(line)
                        pt = p2
                        
                    elif len(l1) == 1:
                        line = l1[0]
                        (p1, p2) = line
                        linesList += [line]
                        oldLine = line
                        points += [p2]
                        allLines.remove(line)
                        pt = p2
                    else:
                        # if AllLines is not empty, then it means we have another poly to find and follow!
                        break
                # End inner while
                points = [x for x in points]
                polyList.append((Blender4CNC.Polytoxogon(points), []))
            # End outer while
            
            # Due to floating point errors, it is possible to end up with orphaned lines or points
            # that appeared to be "extra" polys to follow
    # TEMPORARILY COMMENTED OUT        
            newPolyList = []
            for poly in polyList:
                if len(poly[0].points) >= 2:
                    newPolyList.append(poly)
                else:
                    pass
            polyList = newPolyList
            
            return polyList        
            
        #********************************************************************
        # A poly that is a circle needs to be broken up into 2 semi-circles
        # This function returns the point that is halfway around the circle
        # (opposite the start point)
        #********************************************************************
        def BreakUpCircle(self):
            (p1, p2) = self.points[0:2]
            (cX, cY, CW) = (p2[2:5])
            x = cX - (p1[0] - cX)
            y = cY - (p1[1] - cY)
            newP2 = (x, y, cX, cY, CW)
            return newP2

        #********************************************************************
        # 
        #********************************************************************
        def SameInsideOutside(self, poly2, ls1 = None, ls2 = None):
            # Create list of lines
            xlines1 = self.lines 
            xlines2 = poly2.lines
            
            if ls1 == None:
                # Cut all the poly lines at intersections
                lines1 = self.CutAllLines(xlines1, xlines2)
                lines2 = self.CutAllLines(xlines2, xlines1)
            else:
                lines1 = copy.copy(ls1)
                lines2 = copy.copy(ls2)
            

            poly2IsSame = False
            poly2IsInside = False
            poly2Touches = False
            poly2IsOutside = False

            oldLines2 = copy.copy(lines2)

            self.RemoveSegmentsOnBoundary(lines2)
            oldLines2Boundary = copy.copy(lines2)
            
            if len(lines2) == 0:
                poly2IsSame = True
                return (poly2IsSame, poly2IsInside, poly2Touches, poly2IsOutside)
            
            lines2 = copy.copy(oldLines2Boundary)

            # Remove any lines on poly2 that are inside poly1 OR on the boundary
            oldLen = len(lines2)
            self.RemoveSegmentsOnInside(lines2)
            if len(lines2) == 0:
                poly2IsInside = True
                if self.Overlap(poly2):
                    poly2Touches = True
                return (poly2IsSame, poly2IsInside, poly2Touches, poly2IsOutside)

            lines2 = oldLines2Boundary
            
            self.RemoveSegmentsOnOutside(lines2)
            if len(lines2) == 0:
                poly2IsOutside = True
                if self.Overlap(poly2):
                    poly2Touches = True
                return (poly2IsSame, poly2IsInside, poly2Touches, poly2IsOutside)

            return (poly2IsSame, poly2IsInside, poly2Touches, poly2IsOutside)
            
        def AddSimplifyReturn(self, polyList):
            # Simplify the poly and all tenons
            polyList2 = []
            for item in polyList:
                poly = item[0]
                if poly != None:
                    poly.RemoveSuperfluousStraight()
                    poly.RemoveSuperfluousCurve()
                tenons = item[1]
                tenons2 = []
                for tenon in tenons:
                    if tenon != None:
                        tenon.RemoveSuperfluousStraight()
                        tenon.RemoveSuperfluousCurve()
                    tenons2.append(tenon)
                polyList2.append([poly, tenons2])
            return polyList2
        def Add(self, poly2, infiniteLoopCounter=-1, passingCW = False, selfCW = False, poly2CW = False):
            DEBUG_RARE_FAILURE = False
            if self.points[0] == (0.059, 0.14):
                DEBUG_RARE_FAILURE = True
                indent = ""
            if DEBUG_RARE_FAILURE:
                print("Add function - catching rare failure (trying)")
                self.printPrettyLines(self.lines, indent, "self.lines")
                self.printPrettyLines(poly2.lines, indent, "poly2.lines")

            if passingCW:
                poly1IsCW = selfCW
                poly2IsCW = poly2CW
            else:
                poly1IsCW = self.ImPolyIsClockwise()
                poly2IsCW = poly2.ImPolyIsClockwise()
            
            # If the first poly is counter-clockwise, reverse the two polys, call Add, reverse the result
            if not poly1IsCW and poly2IsCW:
                if DEBUG_RARE_FAILURE:
                    # FAILS COVERAGE
                    print(indent, "1st Poly is CCW")
                raise Blender4CNC.PolyException("Cannot pass CCW poly as 1st poly to Add function", self.points[0])

            # If both polys are CCW
            if not poly1IsCW and not poly2IsCW:
                if DEBUG_RARE_FAILURE:
                    # FAILS COVERAGE
                    print(indent, "1st Poly is CCW and 2nd Poly is CCW")
#                raise Blender4CNC.PolyException("Cannot pass CCW poly as 1st poly to Add function", self.points[0])
                polyA = self.ReverseLineDirections()
                polyB = poly2.ReverseLineDirections()
                result = polyA.Add(polyB, infiniteLoopCounter, True, not poly1IsCW, not poly2IsCW)
                
                polyList = []
                for polyTenons in result:
                    poly = polyTenons[0]
                    # It is not possible for poly to be None at this stage
                    #if poly == None:
                    #    return [polyTenons]
                    polyA = poly.ReverseLineDirections()

                    tenonList = []
                    tenons = polyTenons[1]
                    for tenon in tenons:
                        tenonA = tenon.ReverseLineDirections()
                        tenonList.append(tenonA)
                    if len(tenonList) > 0:
                        polyList.append([tenonList[0], [polyA]])
                    else:
                        polyList.append([None, [polyA]])

                polyList = self.AddSimplifyReturn(polyList)
                return polyList
                
            # So we know that poly1 is clockwise
            
            if DEBUG_RARE_FAILURE:
                print(indent, "1st Poly is CW")

            # Create list of lines
            xlines1 = self.lines #.copy()
            xlines2 = poly2.lines#.copy()
            
            # Cut all the poly lines at intersections
            lines1 = self.CutAllLines(xlines1, xlines2)
            lines2 = self.CutAllLines(xlines2, xlines1)

            (poly2IsSame, poly2IsInside, poly2Touches, poly2IsOutside) = self.SameInsideOutside(poly2, lines1, lines2)
            (poly1IsSame, poly1IsInside, poly1Touches, poly1IsOutside) = poly2.SameInsideOutside(self, lines2, lines1)

            if poly2IsCW:
                if DEBUG_RARE_FAILURE:
                    print(indent, "Both polys CW")
                # Both polys are clockwise!
                
                if poly2IsSame or poly2IsInside:
                    return [[self, []]]
                if poly2IsOutside and not poly2Touches:
                    return [[self, []]]
                if poly2IsOutside and poly2Touches and poly1IsInside:
                    return [[poly2, []]]
                    
                # Remove all inner lines from each poly, then follow the left-most path to add
                # the 2 polys
                    

                poly2.RemoveSegmentsOnInside(lines1)

                self.RemoveSegmentsOnInside(lines2)

                # Remove any overlap lines (from one lists)
                num = 0
                while num < len(lines1):
#                    (removed, same) = self.IsSegmentInListRemoveIt((lines1[num][0], lines1[num][1]), lines2)
                    (removed, same) = self.IsSegmentInListRemoveIt(lines1[num], lines2)
                    if removed:
                        pass
                    else:
                        num += 1

                allLines = lines1 + lines2
                
                allLines = self.RemoveZeroLengthLines(allLines)
                
                # Make polys by following the segments (choosing left-most segment at points of multiple intersections)
                polyList = self.FollowPathOfSegments(allLines, True)

                listOfPolys = [x[0] for x in polyList]
            
                # If we have found more than 1 poly then it means the two polys we joined
                # together have some inner areas 
                # The outer area will be clockwise, the inner areas will be counterclockwise
                ndxCW = -1
                for i in range(0, len(listOfPolys)):
                    # IsClockwise throws an exception if not clockwise!
                    if listOfPolys[i].ImPolyIsClockwise():
                        CW = True
                        ndxCW = i
                        break
                        
            
                outerPoly = listOfPolys[ndxCW]
                listOfPolys.pop(ndxCW)

                # Check if we have any tenons that just touch the outer poly at a single point, if so,
                # make them part of the outline
                polyI = 0
                while polyI < len(listOfPolys):   
                    if outerPoly.Overlap(listOfPolys[polyI]):
                        outerPoly = self.SimpleJoinInternal(outerPoly, listOfPolys[polyI]) 
                        listOfPolys.pop(polyI)
                    else:
                        polyI += 1
                    # end if
                # end while
                
                #return [[outerPoly, listOfPolys]]
                polyList = self.AddSimplifyReturn([[outerPoly, listOfPolys]])
                return polyList
            
            else:
                if DEBUG_RARE_FAILURE:
                    # FAILS COVERAGE
                    print(indent, "2nd Poly is CCW (essentially doing a subtraction)")
                
                # Poly2 is counter-clockwise - we are essentially doing a subtraction
                if poly2IsSame:
                    return [[None, []]]
                if poly2IsOutside:
                    # Does poly2 engulf poly1 or is it merely outside?
                    if poly1IsInside:
                        return [[None, []]]
                    else:
                        return [[self, []]]
#                        return [[self, [poly2]]]
                if poly2IsInside and not poly2Touches:
                    return [[self, [poly2]]]
                    
                # Remove all outer lines from poly2 
                # Remove all inner lines from poly1
                # then follow the left-most path to add
                # the 2 polys
                    
                # Create list of lines
                xlines1 = self.lines #.copy()
                xlines2 = poly2.lines#.copy()
                
                # Cut all the poly lines at intersections
                lines1 = self.CutAllLines(xlines1, xlines2)
                lines2 = self.CutAllLines(xlines2, xlines1)
            
                poly2.RemoveSegmentsOnInside(lines1)
                self.RemoveSegmentsOnOutside(lines2)

                # Remove any overlap lines (from both lists)
                num = 0
                while num < len(lines1):
#                    (removed, same) = self.IsSegmentInListRemoveIt((lines1[num][0], lines1[num][1]), lines2)
                    (removed, same) = self.IsSegmentInListRemoveIt(lines1[num], lines2)
                    if removed:
                        # opposite overlapping lines get removed from both polys
                        if not same:
                            lines1.pop(num)
                        pass
                    else:
                        num += 1

                allLines = lines1 + lines2

                allLines = self.RemoveZeroLengthLines(allLines)

                # Make polys by following the segments (choosing left-most segment at points of multiple intersections)
                polyList = self.FollowPathOfSegments(allLines, True)

                listOfPolys = [x[0] for x in polyList]
            
                # If we have found more than 1 poly then we may have multiple polys and/or multiple tenons
                # The outer areas will be clockwise, the inner areas will be counterclockwise
                ndxCW = -1
                listOfPolys2 = []
                listOfTenons = []
                for i in range(0, len(listOfPolys)):
                    if listOfPolys[i].PolyIsClockwise():
                        listOfPolys2.append(listOfPolys[i])
                    else:
                        listOfTenons.append(listOfPolys[i])
                listOfPolys = listOfPolys2

                # If we have multiple polys - try joining them together at any touching points
                listOfPolys2 = []
                while len(listOfPolys) > 0:
                    outerPoly = listOfPolys[0]
                    listOfPolys.pop(0)
                    polyI = 0
                    while polyI < len(listOfPolys):   
                        if outerPoly.Overlap(listOfPolys[polyI]):
                            # FAILS COVERAGE
                            DRAMATIC_STOP
                            outerPoly = self.SimpleJoinInternal(outerPoly, listOfPolys[polyI]) 
                            listOfPolys.pop(polyI)
                        else:
                            polyI += 1
                        # end if
                    # end while
                    listOfPolys2.append(outerPoly)
                # end while
                listOfPolys = listOfPolys2

                # Did we have tenons? If so, find which polys they belonged to                    
                polyTenons = [[x, []] for x in listOfPolys]
                if len(listOfTenons) > 0:
                    for tenon in listOfTenons:
                        for i in range(0, len(polyTenons)):
                            poly = polyTenons[i][0]
                            if poly.IsPolyCompletelyInside(tenon):
                                polyTenons[i][1].append(tenon)
                                break
                    
                # Now check if any tenons touch their poly - join them
                polyTenons2 = []
                for polyTenon in polyTenons:
                    poly = polyTenon[0]
                    tenons = polyTenon[1]
                    tenonI = 0
                    while tenonI < len(tenons):
                        tenon = tenons[tenonI]
                        if poly.Overlap(tenon):
                            poly = self.SimpleJoinInternal(poly, tenon)
                            tenons.pop(tenonI)
                        else:
                            # FAILS COVERAGE
                            DRAMATIC_STOP
                            tenonI += 1
                    polyTenons2.append([poly, tenons])
                polyTenons = polyTenons2
                
                polyTenons = self.AddSimplifyReturn(polyTenons)
                return polyTenons


        def SimpleJoinInternal(self, poly1, poly2):
    
            # Join the poly (it likely touches more than once)
            # Find a point at which they touch
            # Create list of lines from points
            lines1 = poly1.lines
            lines2 = poly2.lines
            
            
            intersection = None
            for i in range(0, len(lines1)):
                for j in range(0, len(lines2)):
                    ints = self.GetAllIntersections((lines1[i][0], lines1[i][1]), (lines2[j][0], lines2[j][1]))
                    if (ints == inf):
                        # Is this possible?
                        # FAILS COVERAGE
                        print("(ints == inf)")
                        print("lines1[i], lines2[j]=", lines1[i], lines2[j])
                        DRAMATIC_STOP
                        pass
                    elif len(ints) > 0:
                        intersection = ints[0]
                        break
                if intersection != None:
                    break
            # end for
            if intersection == None:
                # FAILS COVERAGE
                DRAMATIC_STOP

            # Find where this point occurs in the outer poly
            for i in range(0, len(poly1.points)):
                if self.PointsAreEqual(poly1.points[i], intersection):
                    outerNdx = i
                    break
                
            # Find where this point occurs in the tenon poly
            for i in range(0, len(poly2.points)):
                if self.PointsAreEqual(poly2.points[i], intersection):
                    innerNdx = i
                    break


            pts1 = poly1.points               
            pts2 = poly2.points
            newPoints = pts1[0:outerNdx+1]
            newPoints += pts2[innerNdx+1:len(pts2)]
            newPoints += pts2[0:innerNdx+1]
            newPoints += pts1[outerNdx+1:len(pts1)]
            newPoints = [x for x in newPoints]
            outerPoly = Blender4CNC.Polytoxogon(newPoints)

            return outerPoly

        
        #********************************************************************
        # Return True if the polytoxogon overlaps this one
        #********************************************************************
        def Overlap(self, tenon2):
            # We have to loop through each segment of tenon1 and see if it crosses
            # or touches any segment of tenon2

            for i in range(0, len(self.lines)):
                for j in range(0, len(tenon2.lines)):
                    ints = self.GetAllIntersections(self.lines[i], tenon2.lines[j])
                    if (ints == inf) or (len(ints) > 0):
                        return True
            return False

        #********************************************************************
        # Take the poly and cut all its lines by the tenon
        # Cut all the lines in the tenon by the poly
        # Return two polys that represent the new lines
        #********************************************************************
        def Create2PolysFromCutLines(self, tenon2):
            # Cut all the poly lines at intersections
            lines1 = self.CutAllLines(self.lines, tenon2.lines)
            lines2 = self.CutAllLines(tenon2.lines, self.lines)
            
            # Create polys from new cut lines
            poly1 = Blender4CNC.Polytoxogon([x[0] for x in lines1])
            poly2 = Blender4CNC.Polytoxogon([x[0] for x in lines2])
            return (poly1, poly2)

        #********************************************************************
        # Check if the poly (tenon2) is totally inside this poly
        # This assumes that all line segments have been cut by the other 
        # poly so that intersections only occur at points.
        # So make sure CutAllLines has been called before calling this function
        #********************************************************************
        def IsPolyCompletelyInside(self, tenon2):
            # Check if all points in tenon2 are inside the poly
            # 0 = out, 1 = in, 2 = on boundary
            locations = []
            for pt in tenon2.points:
                
                if self.IsPointOnBoundary(pt):
                    locations.append(2)
                else:
                    if self.IsPointInside(pt):
                        locations.append(1)
                    else:
                        locations.append(0)

            # Here, locations contains 0,1,2 for every point in tenon2

            # If they are ALL 1, then tenon2 is all inside
            if locations.count(1) == len(locations):
                return True

            # If there are ANY points outside, then the tenon2 is NOT inside
            if locations.count(0) != 0:
                return False

            # If all points are either inside or on the boundary, we MAY have
            # a case where all of tenon2 is inside or we MAY have a WEIRD case
            # where curves are starting and ending on the boundary and are going
            # outside the poly
            # What we need to look for is consecutive boundary points
            for i in range(0,len(locations)):
                j = (i + 1) % len(locations)
                if (locations[i] == 2) and (locations[j] == 2):
                    line = (tenon2.points[i], tenon2.points[j])
                    
#                    midPt = self.GetMidOfSegment((line[0], line[1]))
                    midPt = self.GetMidOfSegment(line)

                    # Is this mid point inside the poly?
                    # If not, then part of tenon2 is outside
                    # Note that some zero length lines that occur with circles can have a mid point on the boundary!
                    if not self.IsPointOnBoundary(midPt):
                        if not self.IsPointInside(midPt):
                            return False
                    
            return True

        #********************************************************************
        # Check if a point is inside the poly
        #********************************************************************
        def IsPointInside(self, ptIn, minMaxStep=1, infLoopCount=100):
            pt = ptIn[0:2]
            
            # Get the bounds of a rectangle that contains this poly
            (minX, minY, maxX, maxY) = self.GetBoundingRectangle()
            
            # Check if we are outside the bounding rectangle first
            if (pt[0] < minX) or (pt[0] > maxX) or (pt[1] < minY) or (pt[1] > maxY):
                return False

            dimX = maxX-minX
            stepX = dimX * 0.1
            dimY = maxY-minY
            stepY = dimY * 0.1

            loopCounter = 0
            while True:
                loopCounter += 1
                if loopCounter > infLoopCount:
                    raise Blender4CNC.PolyException("Infinite loop in IsPointInside", pt)
                origin = (random.uniform(minX-stepX, maxX+stepX), minY-stepY)
                ray = (origin, pt)
                ints = self.IsPointInside_Intersections(ray)
                if type(ints) == list:
                    break
            # ints should contain a set of intersections between the ray and the lines of the poly
            # It could be empty, does it contain an odd number of points?
            odd = len(ints) % 2
            return odd == 1
        #********************************************************************
        # Get all the intersections between a line "ray" and the lines of the
        # poly. If we perfectly overlap a line (inf) or hit end points then
        # we return -1 to signal that this is a problematic ray.
        #********************************************************************
        def IsPointInside_Intersections(self, ray):
            FEQ = Blender4CNC.FloatsAreEqual
            totalInts = []
            for line in self.lines:
                ints = self.GetAllIntersections(ray, line)
                if ints == inf:
                    return -1
                for (a,b) in ints:
                    for p in line:
                        if FEQ(a, p[0]) and FEQ(b, p[1]):
                            return -1
                totalInts += ints
            return totalInts
        #********************************************************************
        # Check if a point lands exactly on one of the segments of the poly
        # boundary
        #********************************************************************
        def IsPointOnBoundary(self, pt):
            # Test each segment of the poly
            for line in self.lines:
                if self.PointIsOnSegment(line, pt):
                    return True
            return False

        #********************************************************************
        # Remove any stubs (Lines that overlap and end at a point)
        #********************************************************************
        def RemoveStubs(self):
            lines = self.lines
            points = self.points
            
            changed = False

            # Remove stubs
            # Loop through all lines
            i = 0

            while i < len(lines):
                
                line1 = lines[i]
                
                # Get the next line
                j = (i + 1) % len(lines)
                line2 = lines[j]
                
                # Get intersections with the line
                ints = self.GetAllIntersections(line1, line2)
                if ints != inf:
                    # No overlap, just increment to next line
                    i += 1
                else:
                    # This must be a stub
                    # Find which line is shorter - this will be the new end point
                    len1 = self.GetLengthOfSegment(line1)
                    len2 = self.GetLengthOfSegment(line2)
                    if len1 == len2:
                        # Both same length - eliminate them both!
                        # Watch out if we are wrapping around
                        if i > j:
                            lines.pop(i)
                            lines.pop(j)
                        else:
                            lines.pop(j)
                            lines.pop(i)
                        # Do not increment i - the same i points to the next line since popping
                        
                        # We may be wrapping around the list
                        if j == 0:
                            i = 0
                        
                        # Maybe we have removed all lines?
                        if len(lines) == 0:
                            changed = True
                            break
                        
                        # Make sure we set the start point of the "next" line (which i points to)
                        prevline = lines[i-1]
                        endP = prevline[1]
                        line2set = (endP, lines[i][1])
                        lines[i] = line2set
                    else:                    
                        #        *-------*
                        #  *-------------*
                        # OR
                        #  *-------------*
                        #        *-------*
                        # Remove line2, line1 will end at end of line2
                        
                        # Change the end point of the current line
                        # If dealing with curves, we need to make sure of the direction we keep
                        if not (len(line1[1]) == 2): # not Segment is straight
                            p = line2[1]
                            if len1 > len2:                        
                                pt2 = (p[0], p[1], p[2], p[3], line1[1][4])
                            else:
                                pt2 = (p[0], p[1], p[2], p[3], line2[1][4])
                            lines[i] = (line1[0], pt2)
                        else:
                            lines[i] = (line1[0], line2[1])
                        # And remove the next line
                        lines.pop(j)

                        # Make sure we set the start point of the "next" line (which "j" points to)
                        # If dealing with curves, we need to make sure of the direction we keep
                        if not (len(line1[1]) == 2): # not Segment is straight
                            p = line2[1]
                            if len1 > len2:                        
                                endP = (p[0], p[1], p[2], p[3], line1[1][4])
                            else:
                                endP = (p[0], p[1], p[2], p[3], line2[1][4])
                        else:
                            endP = line2[1]
                        nextline = lines[j]
                        line2set = (endP, nextline[1])
                        lines[j] = line2set
                        
                    changed = True

                # End if
            # End while
                
            if changed:
                return lines
            else:
                return None
            
        #********************************************************************
        # Return the length of a segment (straight or curved)
        #********************************************************************
        def GetLengthOfSegment(self, line1):
            if len(line1[1]) == 2: # Segment is straight
                (p1,p2) = line1
                v = (p2[0] - p1[0], p2[1] - p1[1]) # p2 - p1
                m = sqrt(v[0]**2 + v[1]**2)
                return m
            else:
                # This is a curve!
                ang = fabs(self.GetCurveAngle(line1))
                (start, end) = self.GetCurveStartEndVector((line1[0], line1[1]))
                m = sqrt(start[0]**2 + start[1]**2)
                return ang * m
                                            
        #********************************************************************
        # Remove any colinear points that are superfluous
        #********************************************************************
        def RemoveSuperfluousColinearPoints(self):
            lines = self.lines
            points = self.points
            changed = False
            i = 0

            while i < len(lines):
                line1 = lines[i]
                
                # Get the next line
                j = (i + 1) % len(lines)
                line2 = lines[j]
                

                if (len(line1[1]) == 2) and (len(line2[1]) == 2): # Segment is straight
                    # We have two straight lines
#                    v1 = self.GetNormalizedVectorOfLine((line1[0], line1[1]))
#                    v2 = self.GetNormalizedVectorOfLine((line2[0], line2[1]))
                    v1 = self.GetNormalizedVectorOfLine(line1)
                    v2 = self.GetNormalizedVectorOfLine(line2)

                    if self.PointsAreEqual(v1, v2):
                        # Co-linear lines - eliminate 2nd line
                        lines[i] = (line1[0], line2[1])
                        lines.pop(j)
                        # Keep i at the same place                    
                        changed = True
                    else:
                        i += 1
                elif not (len(line1[1]) == 2) and not (len(line2[1]) == 2): # not Segment is straight
                    # We have two curves
                    center1 = line1[1][2:4]
                    center2 = line2[1][2:4]
#                    radius1 = self.GetArcRadius((line1[0], line1[1]))
#                    radius2 = self.GetArcRadius((line2[0], line2[1]))
                    radius1 = self.GetArcRadius(line1)
                    radius2 = self.GetArcRadius(line2)
                    dir1 = line1[1][4]
                    dir2 = line2[1][4]
                    if self.PointsAreEqual(center1, center2) and Blender4CNC.FloatsAreEqual(radius1, radius2) and (dir1 == dir2):
                        # "Co-linear" curves - eliminate 2nd curve
                        # We just don't want to convert two semi-circles into one circle!
                        if not (self.PointsAreEqual(line1[0], line2[1]) and self.PointsAreEqual(line1[1], line2[0])):
                            lines[i] = (line1[0], line2[1])
                            lines.pop(j)
                            # Keep i at the same place                    
                            changed = True
                        else:
                            i += 1
                    else:
                        i += 1
                else:
                    i += 1

            if changed:
                return lines
            else:
                return None

        #********************************************************************
        # Given a new set of lines - sets the lines for this poly and 
        # recreate the points in the poly
        #********************************************************************
        def SetLinesRecreatePoints(self, lines2):

#            self.points = [line[0] for line in lines2]
            if len(lines2) > 0:
                self.points = [line[1] for line in lines2]
                self.points = [self.points[-1]] + self.points[0:-1]
            else:
                self.points = []
                
            self.lines = lines2
            
            # Check if this is a circle
            if len(lines2) == 1:
                if (len(lines2[0][0]) == 2) and (len(lines2[0][1]) == 5):
                    self.points.append(lines2[0][1])
            
        #********************************************************************
        # All the lines in lines1 get cut by any intersections with lines
        # in the lines2 list - returns the new list of lines
        #********************************************************************
        def CutAllLines(self, lines1, lines2):
            outLines = []
            
            # Cut all lines in poly1
            for i in range(0, len(lines1)):
                # Get all intersections of this line with any and all lines in other poly
                totalInts = []
                totalInfInts = []
                for j in range(0, len(lines2)):
#                    ints = self.GetAllIntersections((lines1[i][0], lines1[i][1]), (lines2[j][0], lines2[j][1]))
                    ints = self.GetAllIntersections(lines1[i], lines2[j])
                    
                    if ints == inf:
                        # Are any of the start/end points of one line inside the other?
                        A = lines1[i]
                        B = lines2[j]
                        for xp in range(0,2):
#                            if self.PointIsOnAndWithinSegment((A[0], A[1]), B[xp]):
                            if self.PointIsOnAndWithinSegment(A, B[xp]):
                                totalInfInts.append(B[xp])
#                            if self.PointIsOnAndWithinSegment((B[0], B[1]), A[xp]):
                            if self.PointIsOnAndWithinSegment(B, A[xp]):
                                totalInfInts.append(A[xp])
                    else:
                        if len(ints) > 0:
                            totalInts += ints
                        
                # Filter out any intersections that are at the start or end of lines
                start = lines1[i][0]
                end = lines1[i][1]
                totalInts = [int for int in totalInts if (not self.PointsAreEqual(int, start) and (not self.PointsAreEqual(int, end)))]
                totalInfInts = [int for int in totalInfInts if (not self.PointsAreEqual(int, start) and (not self.PointsAreEqual(int, end)))]
                
                totalInts += totalInfInts
                        
                if len(totalInts) > 0:
                    # Order all intersections so the first intersection is closest to beginning of line
#                    newTotalInts = self.OrderIntersections((lines1[i][0], lines1[i][1]), totalInts)
                    newTotalInts = self.OrderIntersections(lines1[i], totalInts)
                    # Filter out duplicates (can happen if the start/end points in the 2nd polygon
                    # land right on a line in 1st polygon
                    
                    filteredInts = []
                    for ii in range(0, len(newTotalInts)-1):
                        if not self.PointsAreEqual(newTotalInts[ii], newTotalInts[ii+1]):
                            filteredInts.append(newTotalInts[ii])
                    filteredInts.append(newTotalInts[-1])
                    
                    cutList = self.CutLineOnIntersections(lines1[i], filteredInts)
                    outLines += cutList
                else:
                    outLines += [lines1[i]]                

            return outLines
                    
        #********************************************************************
        # Order the list of intersection points in order of their proximity
        # to the start of the line.
        # Makes no checks to verify that the intersections are on the line
        #********************************************************************
        def OrderIntersections(self, line, intersections):
            if len(line[1]) == 2: # Straight
                start = line[0]
                # Make a list of all intersections and their distance from start point
                l = []
                for int in intersections:
                    x = int[0] - start[0]
                    y = int[1] - start[1]
                    m = x**2 + y**2 # l3 length^2
                    l.append([m, int])

                # Sort intersections based on length                
                l.sort(key = self.SortIntersections)
            else:
                # This is a curve
                start = (line[0][0], line[0][1])
                (cX, cY) = line[1][2:4]
                startVec = (start[0] - cX, start[1] - cY)
                # Make a list of all intersections and their angles relative to start angle
                l = []
                for int in intersections:
                    vec = (int[0] - cX, int[1] - cY)
                    l.append([self.GetClockwiseAngleBetweenVectors(startVec, vec), int])
                # Sort intersections based on angle
                # If we are going to go in the reverse direction, "0" angles are really 360 degrees!
                if (line[1][4] != 1):
                    l2 = []
                    for i,p in enumerate(l):
                        if Blender4CNC.FloatsAreEqual(p[0],0):
                            p = (math.pi * 2, p[1])
                            l[i] = p
                l.sort(key = self.SortIntersections, reverse = (line[1][4] != 1))
            # Remove extra info
            l2 = [int[1] for int in l]
            return l2

        #********************************************************************
        # Order the list of intersection points in order of their proximity
        # to the start of the line. The list of intersections also 
        # contains a line number that goes with each intersection. If
        # two different lines have the same intersection point, the
        # sort order orders by line number.
        # Makes no checks to verify that the intersections are on the line
        #********************************************************************
        def OrderIntersections2(self, line, intersections):
            if self.PointIsStraight(line[1]):
                start = line[0]
                # Make a list of all intersections and their distance from start point
                l = []
                for int in intersections:
                    l3 = (int[1][0] - start[0], int[1][1] - start[1])
                    m = sqrt(l3[0]**2 + l3[1]**2) # l3 length
                    l4 = [m, int]
                    l.append(l4)
                    
                # Sort intersections based on length                
                l.sort(key = self.SortIntersections2)
            else:
                # This is a curve
                start = (line[0][0], line[0][1])
                center = line[1][2:4]
                startVec = (start[0] - center[0], start[1] - center[1])
                # Make a list of all intersections and their angles relative to start angle
                l = []
                CW = line[1][4]
                for int in intersections:
                    # This returns angles from -pi to pi
                    vec = (int[1][0] - center[0], int[1][1] - center[1])
                    if self.PointsAreEqual(start, int[1]):
                        vec = startVec
                    angle = self.GetClockwiseAngleBetweenVectors(startVec,vec)
                    if CW == 1:
                        l += [[angle, int]]
                    else:
                        if Blender4CNC.FloatsAreEqual(angle, 0):
                            l += [[0, int]]
                        else:
                            l += [[2*pi - angle, int]]
                # Sort intersections based on angle
                l.sort(key = self.SortIntersections2)
            # Remove extra info
            l2 = [int[1] for int in l]
            
            return l2

        #********************************************************************
        # Used for sorting intersections in the OrderIntersections method
        #********************************************************************
        def SortIntersections(self, val): 
            return val[0]  
            
        #********************************************************************
        # Used for sorting intersections in the OrderIntersections2 method
        # We add in the line number as a fraction
        #********************************************************************
        def SortIntersections2(self, val): 
            return (val[0] * 1000) + ((val[1][0]) / 1000)
            
        #********************************************************************
        # Given a line and a list of intersections, returns a list of lines
        # between all the points.
        # It does no checks to verify that the intersections are actually 
        # on the original line
        #********************************************************************
        def CutLineOnIntersections(self, line, intersections):
            newLines = []
            if len(line[1]) == 2: # Segment is straight
                # This is a straight line - 
                # Maybe it has intersected with the END of a curve which has 5 components in the intersection!
                intersections = [(x[0], x[1]) for x in intersections]
                line0_2d = (line[0][0], line[0][1])
                line1_2d = (line[1][0], line[1][1])
                ints = [line0_2d] + intersections + [line1_2d]
                newLines = [(ints[i], ints[i+1]) for i in range(0, len(ints)-1)]
            else:
                # This is a curve
                (start, end) = line
                ints = [start] + intersections + [end]

                # Filter out duplicates (can happen if the start/end points in the 2nd polygon
                # land right on a line in 1st polygon
                # I guess we assume that the list of intersections have been sorted?
                filteredInts = []
                for ii in range(0, len(ints)-1):
                    if not self.PointsAreEqual(ints[ii], ints[ii+1]):
                        filteredInts.append(ints[ii])
                filteredInts.append(ints[-1])
                
    # What about testing last item and 0th element ????????????????
                
                ints = filteredInts
        
                aPoint = (ints[1][0], ints[1][1], end[2], end[3], end[4])
                aLine = (ints[0], aPoint)
                newLines += [aLine]
                for i in range(1, len(ints)-1):
                    aPoint = (ints[i][0], ints[i][1], end[2], end[3], end[4])
                    bPoint = (ints[i+1][0], ints[i+1][1], end[2], end[3], end[4])
                    aLine = (aPoint, bPoint)
                    newLines += [aLine]
            return newLines

        #********************************************************************
        # Returns a vector that is equal to vector v rotated by angle
        # (in radians) in a clockwise direction
        #********************************************************************
        def GoClockwiseAngleVector(self, v, ang):
            v1 = complex(v[0], v[1])
            v2 = cmath.rect(1, ang)
            v1 = v1 * v2.conjugate()
            FEQ = Blender4CNC.FloatsAreEqual
            real = v1.real
            imag = v1.imag
            if FEQ(real,0):
                real = 0
            if FEQ(imag,0):
                imag = 0
            prec = 15
            real = round(real, prec)
            imag = round(imag, prec)
            return (real, imag)

        #********************************************************************
        # With a coordinate system where 0deg = East, 90deg = N, -90 = S etc.
        # returns the angle between two vectors if we travel clockwise from 
        # A to B
        # (angles are in radians)
        #********************************************************************
        def GetClockwiseAngleBetweenVectors(self, A, B):
            FEQ = Blender4CNC.FloatsAreEqual
            if FEQ(A[0], B[0]) and FEQ(A[1], B[1]):
                return 0

            lengthA = sqrt(A[0]**2 + A[1]**2) # A length
            lengthB = sqrt(B[0]**2 + B[1]**2) # B length
            if (lengthA == 0) or (lengthB == 0):
                return nan
            numpy.seterr(invalid='raise')
            Atemp = (A[0], A[1])
            Btemp = (B[0], B[1])
            try:
                t = numpy.dot(Atemp,Btemp)/(lengthA * lengthB)
            except:
                # FAILS COVERAGE
                print("GetClockwiseAngleBetweenVectors looking for RuntimeWarning A,B=", A,B) # FAILS COVERAGE
                DRAMATIC_STOP
            if (t < -1) and Blender4CNC.FloatsAreEqual(t,-1):
                t = -1
            if (t > 1) and Blender4CNC.FloatsAreEqual(t,1):
                # FAILS COVERAGE
                t = 1
            inner=acos(t)
            det = numpy.linalg.det(numpy.array([Atemp,Btemp]))
            if det<0: #this is a property of the det. If the det < 0 then B is clockwise of A
                return inner
            else: # if the det > 0 then A is immediately clockwise of B
                return 2*pi-inner

        #********************************************************************
        # Take a list of polys and shrink them all by 'd' and return new list
        #********************************************************************
        def ShrinkPolys(self,l,d):
            return [p.Shrink(d) for p in l]

        #********************************************************************
        # Take a list of polys and expand them all by 'd' and return new list
        #********************************************************************
        def ExpandPolys(self,l,d):
            return [p.Expand(self, d) for p in l]

        #********************************************************************
        # Check that any curves have equidistant source/destination points
        # from center
        # If there is problem, raises an exception
        # If all is OK, returns None
        #********************************************************************
        def ArcsMakeSense(self):
            for i in range(0,len(self.points)):
                p1 = self.points[i-1]
                p2 = self.points[i]
                if not self.PointIsStraight(p2):
                    (v1, v2) = self.GetCurveStartEndVector((p1, p2))
                    (x,y) = v1
                    lengthV1 = sqrt(x**2 + y**2)
                    (x,y) = v2
                    lengthV2 = sqrt(x**2 + y**2)
                    d = fabs(lengthV1 - lengthV2)
                    if d > 0.0001:
                        str = "ERROR - poly arc segment from %3.4f,%3.4f to %3.4f,%3.4f (point %d)" % (p1[0],p1[1], p2[0],p2[1],i)
                        str += " is invalid (source/destination points are not equidistant from center)"
                        raise Blender4CNC.PolyException(str, (p1[0], p1[1]))
        
        #********************************************************************
        # Get the angle traversed by a curved segment
        #********************************************************************
        def GetCurveAngle(self, l1):
            CW = l1[1][4]        
            if self.PointsAreEqual(l1[0], l1[1]):
                return CW * 2 * pi

            (start, end) = self.GetCurveStartEndVector((l1[0], l1[1]))
            if CW == -1: #Counter-Clockwise
                angle2 = -self.GetClockwiseAngleBetweenVectors(end, start)
            else:
                angle2 = self.GetClockwiseAngleBetweenVectors(start, end)
            return angle2

        #********************************************************************
        # Given a line segment from A to B (vectors), return a line segment 
        # that is parallel to AB and separated by a distance.
        # The result is the same length and the separation distance is
        # measured perpendicular to the original line.
        # If distance > 0 we are getting the "inside" parallel line
        # otherwise return the "outside" (left) parallel line.
        #********************************************************************
        def GetParallelLine(self, line, distance):
            # if we have something like (0,0,0,1,-1) to (0,0) [e.g. from an open path ending where it began]
            # just return the zero-length line
            if self.PointsAreEqual(line[0],line[1]):
                return line
            A = line[0]
            B = line[1]
            AB = (B[0] - A[0], B[1] - A[1]) # AB = B - A
            perp = (AB[1], -AB[0])
            m = sqrt(perp[0]**2 + perp[1]**2) # Length
                
            prec = 15
            AB0 = round(AB[0], prec)
            AB1 = round(AB[1], prec)
            AB = (AB0, AB1)
            perp0 = round(perp[0], prec)
            perp1 = round(perp[1], prec)
            perp = (perp0, perp1)
            m = round(m, prec)
            A0 = round(A[0], prec)
            A1 = round(A[1], prec)
            A = (A0, A1)
            B0 = round(B[0], prec)
            B1 = round(B[1], prec)
            B = (B0, B1)

            perp = (perp[0]/m, perp[1]/m) # Normalize
            perp = (perp[0]*distance, perp[1]*distance)
            AA = (A[0] + perp[0], A[1] + perp[1]) # A + perpendicular
            BB = (B[0] + perp[0], B[1] + perp[1]) # B + perpendicular
            
            # Due to precision, 0.1 - 0.0625 can equal 0.0375000000000000006 so we try to round here!
            prec = 15
            AA0 = round(AA[0], prec)
            AA1 = round(AA[1], prec)
            BB0 = round(BB[0], prec)
            BB1 = round(BB[1], prec)
            AA = (AA0, AA1)
            BB = (BB0, BB1)
            
            return (AA, BB)
        
        #********************************************************************
        # If clockwise curve, get inside parallel curve.
        # If counter-clockwise curve, get outside parallel curve.
        # If distance > 0 we are getting the "inside" parallel line
        # otherwise return the "outside" (left) parallel line.
        #********************************************************************
        def GetParallelCurve(self, line, distance):
            A = line[0]
            CURVE = line[1]

            prec = 15
            if len(A) == 2:
                A = (round(A[0], prec), round(A[1], prec))
            else:
                A = (round(A[0], prec), round(A[1], prec), A[2], A[3], A[4])
            CURVE = (round(CURVE[0], prec), round(CURVE[1], prec), round(CURVE[2], prec), round(CURVE[3], prec), CURVE[4])
            
            Bx = CURVE[0]
            By = CURVE[1]
            (cX, cY) = line[1][2:4]

            # A CW curve can shrink to nothing if the distance is great enough
            if self.PointIsClockwise(CURVE) and (distance > 0): #CW
                x = Bx - cX
                y = By - cY
                m = sqrt(x**2 + y**2) # Length
                if m <= distance:
                    CENTER = line[1][2:4]
                    return (CENTER, CENTER)
            if not self.PointIsClockwise(CURVE) and (distance < 0): #CCW
                x = Bx - cX
                y = By - cY
                m = sqrt(x**2 + y**2) # Length
                if m <= -distance:
                    CENTER = line[1][2:4]
                    return (CENTER, CENTER)
            
            x = A[0] - cX
            y = A[1] - cY
            m = sqrt(x**2 + y**2) # Length

            x = round(x, prec)
            y = round(y, prec)
            m = round(m, prec)

            x *= (m - (CURVE[4]*distance)) / m
            y *= (m - (CURVE[4]*distance)) / m
            x = round(x, prec)
            y = round(y, prec)

            x += cX
            y += cY
            x = round(x, prec)
            y = round(y, prec)

            A2 = (x,y)
            if not self.PointIsStraight(A):
                A2 = (A2[0], A2[1], A[2], A[3], A[4])

            x = Bx - cX
            y = By - cY
            m = sqrt(x**2 + y**2) # Length
            x *= (m - (CURVE[4]*distance)) / m
            y *= (m - (CURVE[4]*distance)) / m
            x += cX
            y += cY
            B2 = (x, y, CURVE[2], CURVE[3], CURVE[4])
            
            # Due to precision, 0.1 - 0.0625 can equal 0.0375000000000000006 so we try to round here!
            prec = 15
            if not self.PointIsStraight(A2):
                A20 = round(A2[0], prec)
                A21 = round(A2[1], prec)
                A22 = round(A2[2], prec)
                A23 = round(A2[3], prec)
                A2 = (A20, A21, A22, A23, A2[4])
            else:
                A20 = round(A2[0], prec)
                A21 = round(A2[1], prec)
                A2 = (A20, A21)
            B20 = round(B2[0], prec)
            B21 = round(B2[1], prec)
            B22 = round(B2[2], prec)
            B23 = round(B2[3], prec)
            B2 = (B20, B21, B22, B23, B2[4])
            
            return (A2, B2)

        #********************************************************************
        # Return the radius of a curve
        #********************************************************************
        def GetArcRadius(self, l):
            x = l[1][0] - l[1][2]
            y = l[1][1] - l[1][3]
            lengthV1 = sqrt(x**2 + y**2) 
            return lengthV1

        #********************************************************************
        # Return a normalized vector of the end of a line/curve 
        #********************************************************************
        def GetEndVector(self, l1):
            (p1, p2) = l1
            if len(p2) == 2: # Straight line
                # p2 - p1
                x = p2[0] - p1[0]
                y = p2[1] - p1[1]
            else:
                # A curve, get tangent to circle at this point
                center = l1[1][2:4]
                CW = p2[4]
                (x,y) = self.GetTangentOnCircleAtPoint(center, p2, CW)
            m = sqrt(x**2 + y**2) # Length
            v1 = (x/m, y/m) # Normalize
            return v1

        #********************************************************************
        # Negate an end vector
        #********************************************************************
        def FlipEndVector(self, v1):
            # If we just do v = -v then we can get -0.0 which can give -pi instead of pi later on with atan2!
            if v1[0] != 0:
                x = -v1[0]
            else:
                x = 0
            if v1[1] != 0:
                y = -v1[1]
            else:
                y = 0
            if len(v1) == 2:
                return (x,y)
            else:
                return (x,y, v1[2], v1[3], v1[4])

        #********************************************************************
        # Return a normalized vector of the start of a line/curve 
        #********************************************************************
        def GetStartVector(self, l1):
            (p1, p2) = l1
            if len(p2) == 2: # Straight line
                # p2 - p1
                x = p2[0] - p1[0]
                y = p2[1] - p1[1]
            else:
                # A curve, get tangent to circle at this point
                center = l1[1][2:4]
                CW = p2[4]
                (x,y) = self.GetTangentOnCircleAtPoint(center, p1, CW)
            m = sqrt(x**2 + y**2) # Length
            v1 = (x/m, y/m) # Normalize
            return v1
        
        #********************************************************************
        # Return a normalized vector that is tangent to a circle at the 
        # given point. If CW_CCW = 1, the returned tangent is in the 
        # clockwise direction
        #********************************************************************
        def GetTangentOnCircleAtPoint(self, center, pt, CW_CCW):
            x = pt[0] - center[0] # pt - center
            y = pt[1] - center[1]
            
            x, y = y, -x # Tangent
            if CW_CCW != 1:
                x = -x # v = -v
                y = -y
                
            # Due to floating point issues, round to zero if close to zero
            if Blender4CNC.FloatsAreEqual(x,0):
                x = 0
            if Blender4CNC.FloatsAreEqual(y,0):
                y = 0
            
            m = sqrt(x**2 + y**2) # Length
            v = (x/m, y/m) # Normalize
            return v

        #********************************************************************
        # Returns intersection of two line segments (which may be straight or 
        # curved). Returns [] if there is no intersection.
        #********************************************************************
        def GetAllIntersections(self, A, B):
                
            FEQ = Blender4CNC.FloatsAreEqual
            # For things like circles, sometimes we get a "segment" that is from a curve point back to the same 2d point
            # The length of this line is 0 and messes up functions like Overlap
            # These lines should be ignored
            (A0, A1) = A
            (B0, B1) = B
            if (len(A0) > 2) and (len(A1) == 2):
                if FEQ(A0[0], A1[0]) and FEQ(A0[1], A1[1]):
                    return []
            if (len(B0) > 2) and (len(B1) == 2):
                if FEQ(B0[0], B1[0]) and FEQ(B0[1], B1[1]):
                    return []

            Aline = (len(A1) == 2)
            Bline = (len(B1) == 2)

            if Aline and Bline: # Two lines
                # Check if the two lines overlie each other and therefore have infinite points
                if self.LineSegmentsOverlap(A,B):
                    return inf
                
                # There are cases when we have two line segments which touch
                # each other at an end point - sometimes the floating point math would stop the blender
                # function intersect_line_line_2d from detecting an intersection
                # A[0] == B[1]
                if FEQ(A0[0], B1[0]) and FEQ(A0[1], B1[1]):
                    return [A0]
                # A[1] == B[0]
                if FEQ(A1[0], B0[0]) and FEQ(A1[1], B0[1]):
                    return [A1]
                
                ints = []

                ret = self.GetIntersectionBetweenTwoStraightSegments(A,B)
                if type(ret) != type(None):
                    ints = [ret]
            elif Aline and not Bline: # This is a line and curve
                ints = self.GetIntersectionsBetweenLineAndArc(A,B)
            elif not Aline and Bline: # This is a curve and line
                ints = self.GetIntersectionsBetweenLineAndArc(B,A)
            else: # Two curves
                ints = self.GetIntersectionsBetweenTwoArcs(A,B)
            if ints != inf:
                if len(ints) > 0:
                    ints2 = []
                    for ret in ints:
                        if self.PointsAreEqual(ret, A0):
                            ints2.append(A0)
                        elif self.PointsAreEqual(ret, A1):
                            ints2.append(A1)
                        elif self.PointsAreEqual(ret, B0):
                            ints2.append(B0)
                        elif self.PointsAreEqual(ret, B1):
                            ints2.append(B1)
                        else:            
                            ints2.append(ret)
                    ints = ints2
                ints = [x[0:2] for x in ints]
            return ints

        #********************************************************************
        # Gets the intersection between a straight line and a circle
        # Returns [] if no intersection
        #********************************************************************
        def GetIntersectionsBetweenLineAndCircle(self, A, B):
            # If A is a vertical line
            (A0, A1) = A
            (B0, B1) = B
            if Blender4CNC.FloatsAreEqual(A1[0], A0[0]):
                # Rotate by 90 degrees
                A2 = self.RotateSegment90Degrees(A)
                B2 = self.RotateSegment90Degrees(B)
                ints = self.GetIntersectionsBetweenLineAndCircle(A2,B2)
                # Rotate -90 degrees or 270 degrees
                for i in range(0,len(ints)):
                    for j in range(0,3):
                        ints[i] = self.RotatePoint90Degrees(ints[i])
                return ints
            
            a0x = A0[0]
            a0y = A0[1]
            
            # The 1st line A, y = mx + C
            # m = dy / dx
            m = (A1[1] - a0y) / (A1[0] - a0x)
            # C = y - mx
            C = a0y - m * a0x
            
            prec = 15
            m = round(m, prec)
            C = round(C, prec)

            # The 2nd curve B, (x - xCenter)^2 + (y - yCenter)^2 = r^2
            centerX = B1[2]
            centerY = B1[3]
            dx = B1[0] - centerX
            dy = B1[1] - centerY
            dx = round(dx, prec)
            dy = round(dy, prec)
            rr = dx**2 + dy**2
            rr = round(rr, prec)
            
            # Average radius from two points to help eliminate math precision problems
            dx = B0[0] - centerX
            dy = B0[1] - centerY
            dx = round(dx, prec)
            dy = round(dy, prec)
            rrB = dx**2 + dy**2
            rrB = round(rrB, prec)
            rr = (rr + rrB)/2
            rr = round(rr, prec)


            solve = self.SolveQuadratic(m,C,centerX,centerY,rr)


            if solve == None:
                # Due to floating point math precision must check if one curve exactly begins/ends where the other
                # begins/ends 
                ret = self.GetCurveCurveSpecialInts(A, B)
                return ret
            
            (x1,x2) = solve
            
            # y = mx + C
            y1 = m * x1 + C
            y2 = m * x2 + C

            x1 = round(x1, prec)
            x2 = round(x2, prec)
            y1 = round(y1, prec)
            y2 = round(y2, prec)

            if Blender4CNC.FloatsAreEqual(x1,x2) and Blender4CNC.FloatsAreEqual(y1,y2):
                return [(x1,y1)]

            return [(x1,y1),(x2,y2)]

        #********************************************************************
        # Gets the intersection between 2 straight lines
        # Returns [] if no intersection
        #********************************************************************
        def GetIntersectionBetweenTwoStraightSegments(self, A, B):
#            int = self.GetIntersectionBetweenLineAndLine((A[0], A[1]), (B[0], B[1]))
            int = self.GetIntersectionBetweenLineAndLine(A, B)
#            if type(int) == type(None):
            if int == None:
                return None
            if int == inf:
#            if (type(int) == type(inf)) and (int == inf):
                return inf
            ints = self.CheckPointsAreOnStraightSegment(A, [int])
            if len(ints) > 0:
                ints = self.CheckPointsAreOnStraightSegment(B, ints)
                if len(ints) > 0:
                    return ints[0]
            return None

        def GetIntersectionBetweenLineAndLine(self, A, B):

            a0x = A[0][0]
            a0y = A[0][1]
            a1x = A[1][0]
            a1y = A[1][1]
            b0x = B[0][0]
            b0y = B[0][1]
            b1x = B[1][0]
            b1y = B[1][1]
            FEQ = Blender4CNC.FloatsAreEqual

            # Make sure the line is not of 0 length!
            # A[1] == A[0]
            axEqual = FEQ(a1x, a0x)
            ayEqual = FEQ(a1y, a0y)
            if axEqual and ayEqual:
                return None
            bxEqual = FEQ(b1x, b0x)
            byEqual = FEQ(b1y, b0y)
            # B[1] == B[0]
            if bxEqual and byEqual:
                return None

            # If both are vertical lines, either there are no intersections or infinite
            if axEqual and bxEqual:
                if FEQ(a0x, b0x):
                    # Do they overlap, or just touch at a point
                    ay1 = a0y
                    ay2 = a1y
                    if ay1 > ay2:
                        (ay1, ay2) = (ay2, ay1)
                    by1 = b0y
                    by2 = b1y
                    if by1 > by2:
                        (by1, by2) = (by2, by1)
                    if FEQ(ay1, by2):
                        return (a0x, ay1)
                    if FEQ(ay2, by1):
                        return (a0x, ay2)
                    if ay1 > by2:
                        return None                
                    if by1 > ay2:
                        return None                
                    return inf
                else:
                    return None

            # If both are horizontal lines, either there are no intersections or infinite
            if ayEqual and byEqual:
                if FEQ(a0y, b0y):
                    # Do they overlap, or just touch at a point
                    ax1 = a0x
                    ax2 = a1x
                    if ax1 > ax2:
                        (ax1, ax2) = (ax2, ax1)
                    bx1 = b0x
                    bx2 = b1x
                    if bx1 > bx2:
                        (bx1, bx2) = (bx2, bx1)
                    if FEQ(ax1, bx2):
                        return (ax1, b0y)
                    if FEQ(ax2, bx1):
                        return (ax2, b0y)
                    if ax1 > bx2:
                        return None                
                    if bx1 > ax2:
                        return None                
                    return inf
                else:
                    return None

            # If A is a vertical line
            if axEqual:
                x = a0x
                m2 = (b1y - b0y) / (b1x - b0x)
                C2 = b0y - m2 * b0x
                y = m2 * x + C2
                return (x,y)
            
            # If B is a vertical line
            if bxEqual:
                x = b0x
                m1 = (a1y - a0y) / (a1x - a0x)
                C1 = a0y - m1 * a0x
                y = m1 * x + C1
                return (x,y)

            
            # The 1st line A, y = mx + C
            # m = dy / dx
            m1 = (a1y - a0y) / (a1x - a0x)
            # C = y - mx
            C1 = a0y - m1 * a0x

            # The 2nd line B, y = mx + C
            # m = dy / dx
            m2 = (b1y - b0y) / (b1x - b0x)
            # C = y - mx
            C2 = b0y - m2 * b0x

            # The intersection occurs at x = (c2-c1)/(m1-m2)
            # If the gradients are the same - parallel!
            if FEQ(m1,m2):
                # Parallel lines!
                return None

            
            prec = 15
            x = (C2-C1)/(m1-m2)
            x = round(x, prec)
            y = m1 * x
            y = round(y, prec)
            y = y + C1
            y = round(y, prec)
            return (x,y)
                
            
        #********************************************************************
        # Gets the intersection between a straight line and a curved segment
        # Returns [] if no intersection
        #********************************************************************
        def GetIntersectionsBetweenLineAndArc(self, A, B):

            # Make sure the line is not of 0 length!
            if self.PointsAreEqual(A[1], A[0]):
                return []
                
#            ints = self.GetIntersectionsBetweenLineAndCircle((A[0], A[1]),(B[0], B[1]))
            ints = self.GetIntersectionsBetweenLineAndCircle(A,B)
            ints = self.CheckPointsAreOnStraightSegment(A, ints)
            if len(ints) > 0:
                ints = self.CheckPointsAreOnCurve(B, ints)
            

            if len(ints) == 0:
                # Due to floating point math precision must check if one curve exactly begins/ends where the other begins/ends
#                ret = self.GetCurveCurveSpecialInts((A[0], A[1]), (B[0], B[1]))
                ret = self.GetCurveCurveSpecialInts(A, B)
                return ret
            return ints

        #********************************************************************
        # Called from GetIntersectionsBetweenLineAndArc, it is assumed
        # that the points are already proven to be on the infinite line
        #********************************************************************
        def CheckPointsAreOnStraightSegment(self, A, ints):
            tol = Blender4CNC.REL_TOLERANCE
            ax = A[0][0]
            bx = A[1][0]
            if ax < bx:
                xMin = ax-tol
                xMax = bx+tol
            else:
                xMin = bx-tol
                xMax = ax+tol
            ay = A[0][1]
            by = A[1][1]
            if ay < by:
                yMin = ay-tol
                yMax = by+tol
            else:
                yMin = by-tol
                yMax = ay+tol
                
            newInts = []
            for int in ints:
                a = int[0]
                if (a >= xMin) and (a <= xMax):
                    b = int[1]
                    if (b >= yMin) and (b <= yMax):
                        newInts.append(int)
            return newInts

        #********************************************************************
        # Gets the intersection between two curved segments
        # Returns None if no intersection
        # ALSO Returns None if infinite intersections - i.e. two curves
        # lie on the same circle and overlap 
        #********************************************************************
        def GetIntersectionsBetweenTwoArcs(self, A, B):

            FEQ = Blender4CNC.FloatsAreEqual
            circleInts = self.GetIntersectionsBetweenTwoCircles(A,B)

            # Check if the two circles are on the same center!
            if circleInts == inf:

                # Two curves may lie on the same circle - they could have no overlap, touch at a single
                # point, or touch at two individual points, or overlap for an infinite number of points
                p1 = (A[0][0], A[0][1])
                p2 = (A[1][0], A[1][1])
                p3 = (B[0][0], B[0][1])
                p4 = (B[1][0], B[1][1])
                    
                # Test for two touches
                # There is a possibility that they exactly overlap each other!
                # (p1 == p3) and (p2 == p4)
                if FEQ(p1[0], p3[0]) and FEQ(p1[1], p3[1]):
                    if FEQ(p2[0], p4[0]) and FEQ(p2[1], p4[1]):
                        # They start and end at the same points, same center, are they same direction?
                        if A[1][4] == B[1][4]:
                            return inf
                        else:
                            return [p1, p2]
                # (p1 == p4) and (p2 == p3)
                if FEQ(p1[0], p4[0]) and FEQ(p1[1], p4[1]):
                    if FEQ(p2[0], p3[0]) and FEQ(p2[1], p3[1]):
                        # They start where the other ends, same center, are they both in opposite directions?
                        if A[1][4] != B[1][4]:
                            return inf
                        else:
                            return [p1, p2]

                # Test for one touch
                # (p1 == p3)
                if FEQ(p1[0], p3[0]) and FEQ(p1[1], p3[1]):
                    if self.IsPointOnCurve(A, p4):
                        return inf # They start on same point, but the other ends of the curves overlap
                    elif self.IsPointOnCurve(B, p2):
                        return inf
                    else:
                        return [p1]
                # (p2 == p4):
                if FEQ(p2[0], p4[0]) and FEQ(p2[1], p4[1]):
                    if self.IsPointOnCurve(A, p3):
                        return inf # They end on same point, but the other ends of the curves overlap
                    elif self.IsPointOnCurve(B, p1):
                        return inf 
                    else:
                        return [p2]
                # (p2 == p3):
                if FEQ(p2[0], p3[0]) and FEQ(p2[1], p3[1]):
                    if self.IsPointOnCurve(A, p4):
                        return inf # The first curve ends where the 2nd starts, but the 2nd ends overlapping
                    elif self.IsPointOnCurve(B, p1):
                        return inf # The 2nd curve comes back and goes past the start of line1
                    return [p2]
                # (p4 == p1):
                if FEQ(p1[0], p4[0]) and FEQ(p1[1], p4[1]):
                    if self.IsPointOnCurve(A, p3):
                        return inf # The 2nd curve ends where the first starts, but the 2nd starts overlapping the start of the 2nd
                    elif self.IsPointOnCurve(B, p2):
                        # For the circumstance where two arcs lie on the same circle with inf 
                        # intersections, if B ends where A starts and there is overlap on the other
                        # ends of the arcs, then this is caught above with p3 on A before we
                        # can get to check if p2 is on B
                        # FAILS COVERAGE
                        return inf # The 2nd curve ends where the first starts, but the first ends overlapping the start of the 2nd
                    else:
                        return [p1]
                
                # At this point, the two curves do not start or end at the exact start or end of
                # each other, but they may still overlap
                if self.IsPointOnCurve(A, p3):
                    # We know the two arcs are concentric and neither start or end exactly at the
                    # start or end of the other, if p3 is on A, the intersection is inf!
                    return inf
                if self.IsPointOnCurve(A, p4):
                    return inf
                # After testing if B starts or ends inside arc A, we only need to test one of the A
                # points inside B
                if self.IsPointOnCurve(B, p1):
                    return inf
                #if self.IsPointOnCurve(B, p2):
                #    return inf

                # The two curves do not overlap            
                return []
            # END if the two circles are on the same center!

            ints = circleInts
            # Due to floating point math precision must check if one curve exactly begins/ends where the other begins/ends
            specialInts = self.GetCurveCurveSpecialInts(A, B)

            # Only add in non-duplicate points
            for specialP in specialInts:
                dup = False
                for point in ints:
                    if self.PointsAreEqual(specialP, point):
                        dup = True
                        break
                if not dup:
                    ints.append(specialP)  
            
            # Must check points are on the arcs
            ints = self.CheckPointsAreOnCurve(A, ints)
            ints = self.CheckPointsAreOnCurve(B, ints)
                
            return ints

        #********************************************************************
        # Get 0,1, or 2 intersections between two circles
        #********************************************************************
        def GetIntersectionsBetweenTwoCircles(self, A, B):
                
            # To help minimize errors in floating point, use both points -> center to 
            # get an average for the radius of each circle
                
            # The 1st curve A, (x - e)^2 + (y - f)^2 = r^2
            # where e,f is the center
            centerA = A[1][2:4]
            dx0 = A[0][0] - centerA[0] 
            dy0 = A[0][1] - centerA[1]
            dx1 = A[1][0] - centerA[0] 
            dy1 = A[1][1] - centerA[1]
            
            r0 = sqrt(dx0**2 + dy0**2)
            r1 = sqrt(dx1**2 + dy1**2)
            
            r = (r0+r1)/2
            
            # The 2nd curve B, (x - g)^2 + (y - h)^2 = s^2
            # where g,h is the center
            centerB = B[1][2:4]
            dx0 = B[0][0] - centerB[0] 
            dy0 = B[0][1] - centerB[1]
            dx1 = B[1][0] - centerB[0] 
            dy1 = B[1][1] - centerB[1]
            
            s0 = sqrt(dx0**2 + dy0**2)
            s1 = sqrt(dx1**2 + dy1**2)
            
            s = (s0+s1)/2

            # Check that circles will intersect, or are exact overlaps
            v = (centerA[0]-centerB[0], centerA[1]-centerB[1]) # centerA - centerB
            d = sqrt(v[0]**2 + v[1]**2)
            d2 = (v[0]/2)**2 + (v[1]/2)**2
            if (d > (r + s)) and not Blender4CNC.FloatsAreEqual(d, r+s):
                return []
            if d < fabs(r - s) and not Blender4CNC.FloatsAreEqual(d, fabs(r - s)):
                return []
            if Blender4CNC.FloatsAreEqual(d2, 0):
                # The case where there are two concentric circles with different radii gets caught above
                # with d < fabs(r-s)
                return inf

            # If d equals r+s, there will be only 1 intersection
            if Blender4CNC.FloatsAreEqual(d, r+s):
                # r*r - s*s + (r+s)*(r+s) / (2 * (r+s))
                # => r*r - s*s + r*r + 2rs + s*s / (2 (r+s))
                # => 2 (r*r + rs) / (2 (r+s))
                # => (r*r + rs) / (r+s)
                # => r(r + s) / (r+s)
                # => r
                a = r
            else:
                a = (r*r - s*s + d*d) / (2 * d)
                
            a2 = a**2
            if Blender4CNC.FloatsAreEqual(r*r, a2):
                h = 0
            # A weird case where d IS actually less than fabs(r-s) BUT is so close to the edge
            # that it gets past the above checks and would try to sqrt a negative number!
            elif d < fabs(r - s) and Blender4CNC.FloatsAreEqual(d, fabs(r - s)):
                h = 0
            else:
                h = math.sqrt(r*r - a2)

            (ax, ay) = centerA
            (bx, by) = centerB
            px = ax + (a * (bx - ax) / d)
            py = ay + (a * (by - ay) / d)
            P2 = (px, py)
            
            (x2,y2) = P2
            
            (x0, y0) = centerA
            (x1, y1) = centerB

            x3 = x2 + h * ( y1 - y0 ) / d
            y3 = y2 - h * ( x1 - x0 ) / d

            x4 = x2 - h * ( y1 - y0 ) / d
            y4 = y2 + h * ( x1 - x0 ) / d
            
            P3 = (x3,y3)
            P4 = (x4,y4)
            if self.PointsAreEqual(P3, P4):
                return [P3]
            return [P3, P4]

        #********************************************************************
        # Due to floating point math precision must check if one curve exactly begins/ends where the other begins/ends 
        #********************************************************************
        def GetCurveCurveSpecialInts(self, A, B):

            ret = []     
            FEQ = Blender4CNC.FloatsAreEqual   

            for a in A:
                for b in B:
                    if FEQ(a[0], b[0]) and FEQ(a[1], b[1]):
                        ret.append((a[0], a[1]))
            return ret

        #********************************************************************
        # Rotates a line (straight or curve) by 90 degrees clockwise
        #********************************************************************
        def RotateSegment90Degrees(self, A):
            return [ self.RotatePoint90Degrees(x) for x in A]

        #********************************************************************
        # Rotates a point (straight or curve) by 90 degrees clockwise
        #********************************************************************
        def RotatePoint90Degrees(self, A):
            if len(A) == 2: # Line
                return (A[1], -A[0])
            else: # Curve
                return (A[1], -A[0], A[3], -A[2], A[4])

        #********************************************************************
        # Solves the quadratic equation from a line and circle equation to
        # return the x values where they touch
        # line: y = mx + C
        # circle: (x - xCenter)^2 + (y - yCenter) ^2 = rr 
        # rr is radius squared!
        # Returns None if there is no intersection, otherwise returns a tuple
        # of x locations - if there is just one point, then both values in the
        # tuple are the same.
        # Cannot deal with vertical lines (m is infinite)
        #********************************************************************
        def SolveQuadratic(self, m, C, xCenter, yCenter, rr):
            # Get the coeffs of quadratic
            a = 1 + m * m
            b = 2 * m * C - 2 * xCenter - 2 * m * yCenter
            c = xCenter * xCenter + C * C + yCenter * yCenter - 2 * C * yCenter - rr
            # It should be impossible for a to ever equal zero
            #if Blender4CNC.FloatsAreEqual(a, 0.0):
            #    a = 0.0
            if Blender4CNC.FloatsAreEqual(b, 0.0):
                b = 0.0
            if Blender4CNC.FloatsAreEqual(c, 0.0):
                c = 0.0
                        
            # Solve quadratic
            b2_4ac = b * b - 4 * a * c
            if Blender4CNC.FloatsAreEqual(b2_4ac, 0.0):
                b2_4ac = 0.0
            # If b2_4ac < 0 we are in trouble !
            if b2_4ac < 0:
                b2_4ac = self.ClampIfEqualZeroWithError(b2_4ac)
            if b2_4ac < 0:
                return None
            sqrt_b2_4ac = math.sqrt(b2_4ac)
            x1 = (-b + sqrt_b2_4ac) / (2 * a)
            x2 = (-b - sqrt_b2_4ac) / (2 * a)
            
            return (x1,x2)

        #********************************************************************
        # Returns True if a is between b and c (allowing for some slight
        # error margin) 
        #********************************************************************
        def BetweenwithError(self, a,b,c):
            return ((a >= (b-Blender4CNC.REL_TOLERANCE)) and (a <= (c+Blender4CNC.REL_TOLERANCE)))

        #********************************************************************
        # Returns 0 if the value is VERY VERY close to 0
        #********************************************************************
        def ClampIfEqualZeroWithError(self, xs):
            if (xs > -Blender4CNC.REL_TOLERANCE) and (xs < Blender4CNC.REL_TOLERANCE):
                return 0
            return xs

        #*************************************************************************
        # Returns True if the bounding rectangles of the two polys overlap
        #*************************************************************************
        def BoundingRectanglesOverlap(self, poly2):
            (minX, minY, maxX, maxY) = self.GetBoundingRectangle()
            (minX2, minY2, maxX2, maxY2) = poly2.GetBoundingRectangle()

            p = [(minX, minY), (minX, maxY), (maxX, maxY), (maxX, minY)]
            p2 = [(minX2, minY2), (minX2, maxY2), (maxX2, maxY2), (maxX2, minY2)]

            # Check if end points match (floating precision can miss this in intersect_line_line_2d)
            p3 = [self.PointsAreEqual(i,j) for i in p for j in p2]
            if True in p3:
                return True

            if self.PointIsInsideRectangle(minX2, minY2, (minX, minY, maxX, maxY)):
                return True
            if self.PointIsInsideRectangle(minX2, maxY2, (minX, minY, maxX, maxY)):
                return True
            if self.PointIsInsideRectangle(maxX2, minY2, (minX, minY, maxX, maxY)):
                return True
            if self.PointIsInsideRectangle(maxX2, maxY2, (minX, minY, maxX, maxY)):
                return True
            
            # Pair up the points into lines
            lines = [x for x in zip(p, p[-1:] + p[:-1])]
            lines2 = [x for x in zip(p2, p2[-1:] + p2[:-1])]
            
            for A in lines:
                for B in lines2:
                    ret = self.GetIntersectionBetweenTwoStraightSegments(A, B)
                    if ret:
                        return True
            
            return False        

        #*************************************************************************
        # Return True if the point x,y is inside the rectangle
        #*************************************************************************
        def PointIsInsideRectangle(self, x, y, rect):
            (minX, minY, maxX, maxY) = rect
            return (x >= minX) and (x <= maxX) and (y >= minY) and (y <= maxY)
            
        #********************************************************************
        # After expanding, the tenons may overlap with the edge of the pocket
        # Note that we do not care about any tenons that are completely INSIDE the poly!
        # therefore, the subtract function can never return any polys with tenons!
        #********************************************************************
        def SubtractEdgeTenonsFromPoly(self, finalPoly, finalTenonsList):

            polyList = [finalPoly]
            newTenonsList = []

            for tenon in finalTenonsList:
                polyList2 = []
                tenonUsed = False
                for poly in polyList:
                    if not poly.BoundingRectanglesOverlap(tenon):
                        polyList2.append(poly)
                        continue
                    
                    if not poly.Overlap(tenon):
                        polyList2.append(poly)
                        continue

                    # They overlap, so subtract the tenon from the poly
                    # The result can be multiple polys (there cannot ever be tenons created)
                    tenonUsed = True
                    result = poly.Subtract(tenon)
                    polyList2 += [x[0] for x in result]
                    
                polyList = polyList2
                if not tenonUsed:
                    newTenonsList.append(tenon)

            return (polyList, newTenonsList)

        #********************************************************************
        # Returns the rectangle that encloses the polytoxogon
        #********************************************************************
        def GetBoundingRectangle(self):  
            pointsX = []
            pointsY = []
            for i in range(0,len(self.points)):
                p = self.points[i]
                if len(p) != 2: # Curve
                    prevP = self.points[i-1]
                    (minXC, minYC, maxXC, maxYC) = self.GetMinMaxCurve(prevP, p)
                    pointsX.append(minXC)
                    pointsX.append(maxXC)
                    pointsY.append(minYC)
                    pointsY.append(maxYC)
                else:
                    pointsX.append(p[0])
                    pointsY.append(p[1])
            minX = min(pointsX)
            maxX = max(pointsX)
            minY = min(pointsY)
            maxY = max(pointsY)

            return (minX, minY, maxX, maxY)
        #********************************************************************
        # Returns the rectangle that encloses the polytoxogon
        # Treats arcs as circles
        #********************************************************************
        def GetBoundingRectangleNonExact(self):  

            pointsX = []
            pointsY = []
            for i in range(0,len(self.points)):
                p = self.points[i]
                if len(p) != 2: # Curve
                    prevP = self.points[i-1]
                    (minXC, minYC, maxXC, maxYC) = self.GetMinMaxCurveNonExact(prevP, p)
                    pointsX.append(minXC)
                    pointsX.append(maxXC)
                    pointsY.append(minYC)
                    pointsY.append(maxYC)
                else:
                    pointsX.append(p[0])
                    pointsY.append(p[1])
            minX = min(pointsX)
            maxX = max(pointsX)
            minY = min(pointsY)
            maxY = max(pointsY)
            return (minX, minY, maxX, maxY)

        #********************************************************************
        # Get the two vectors that represent the start and end of the curve
        #********************************************************************
        def GetCurveStartEndVector(self, B):
            center = B[1][2:4]
            vA = (B[0][0] - center[0], B[0][1] - center[1]) # B0 - center
            vB = (B[1][0] - center[0], B[1][1] - center[1]) # B1 - center
            return (vA, vB)

        #********************************************************************
        # Convert a line into a text readable form
        #********************************************************************
        def ConvertLineToString(self, line):
            str = "%3.4f,%3.4f to %3.4f,%3.4f" % (line[0][0], line[0][1], line[1][0], line[1][1])
            return str

        #********************************************************************
        # Get the angle to a point on the curve
        # Note: no checks are done to make sure that the point is actually ON
        # the curve!
        #********************************************************************
        def GetCurveAngleAtPoint(self, B, p):
            vx = p[0] - B[1][2] # Get point minus center
            vy = p[1] - B[1][3]
            ans = atan2(vy, vx)
            return ans

        #********************************************************************
        # Returns True if point is a clockwise curve
        #********************************************************************
        def PointIsClockwise(self, p):
            return p[4] == 1
                
        #********************************************************************
        # Clip an angle to be between -pi and pi
        #********************************************************************
        def ClipAnglePlusMinusPi(self, a):
            while a > pi:
                a -= 2*pi
            while a < -pi:
                a += 2*pi
            return a

        #********************************************************************
        # Returns True if the points is on the arc - the end points of the
        # arc are included!
        #********************************************************************
        def IsPointOnCurve(self, B, p):
            px = p[0]
            py = p[1]
            B0 = B[0]
            B1 = B[1]
            centerX = B1[2]
            centerY = B1[3]

            # Check first if the point is at the start or end of the curve
            FEQ = Blender4CNC.FloatsAreEqual
            if FEQ(px, B[0][0]) and FEQ(py, B[0][1]):
                return True
            if FEQ(px, B[1][0]) and FEQ(py, B[1][1]):
                return True

            # Check if the point is the same distance from the center point
            dx = B0[0] - centerX
            dy = B0[1] - centerY
            radius = math.sqrt(dx**2 + dy**2)
            radiusSqrd = dx**2 + dy**2
            dx = B1[0] - centerX
            dy = B1[1] - centerY
            radius2 = math.sqrt(dx**2 + dy**2)
            radius2Sqrd = dx**2 + dy**2
            radiusFinalSqrd = (radiusSqrd+radius2Sqrd)/2
            dx = px - centerX
            dy = py - centerY
            dist = math.sqrt(dx**2 + dy**2)
            distSqrd = dx**2 + dy**2
            if not FEQ(radiusFinalSqrd, distSqrd):     
                return False


            # GetCurveAngleAtPoint
            vx = B0[0] - centerX 
            vy = B0[1] - centerY
            angA = atan2(vy, vx)

            # GetCurveAngleAtPoint
            vx = px - centerX 
            vy = py - centerY
            ang = atan2(vy, vx)

            
            # First check if the point is VERY close to one of the curve end points.
            # It has happened that a point was SLIGHTLY behind the start of a CCW curve and after the angles
            # were rotated, the start was at -pi and the point was at +pi!
            if FEQ(ang, angA):
                # FAILS COVERAGE
                return True

            # GetCurveAngleAtPoint
            vx = B1[0] - centerX 
            vy = B1[1] - centerY
            angB = atan2(vy, vx)

            if FEQ(ang, angB):
                return True

            if B[1][4] == 1: # Clockwise

                if angA > angB:
                    return Blender4CNC.FloatIsBetween(ang, angB, angA)
                else:
                    return not Blender4CNC.FloatIsBetween(ang, angA, angB)
            else:

                if angA < angB:
                    return Blender4CNC.FloatIsBetween(ang, angA, angB)
                else:
                    return not Blender4CNC.FloatIsBetween(ang, angB, angA)

        #********************************************************************
        # Returns a list of only the points that are on the curve
        #********************************************************************
        def CheckPointsAreOnCurve(self, B, ints):
            if ints != None:
                ret = []
                for x in ints:
                    if ((not x is None) and self.IsPointOnCurve((B[0], B[1]), x)):
                        ret.append(x)
                return ret
            return ints

        #********************************************************************
        # Gets the x,y coordinates of a rectangle that encloses the curve 
        # from p1 to p2
        #********************************************************************
        def GetMinMaxCurve(self, p1, p2):        
            centerX = p2[2]
            centerY = p2[3]
            dx = centerX - p1[0]
            dy = centerY - p1[1]
            radius = math.sqrt(dx**2 + dy**2)

            # GetCurveAngleAtPoint
            vx = p1[0] - centerX 
            vy = p1[1] - centerY
            angA = atan2(vy, vx)
            # GetCurveAngleAtPoint
            vx = p2[0] - centerX 
            vy = p2[1] - centerY
            angB = atan2(vy, vx)

            # If counter-clockwise
            if p2[4] == -1:
                (angA, angB) = (angB, angA)
            
            # Convert angle to a quad 1 0
            #                         2 3
            qA = (angA + math.pi) / (math.pi/2)
            qA = (int(qA + 2) % 4)

            qB = (angB + math.pi) / (math.pi/2)
            qB = (int(qB + 2) % 4)
            
            # Assume the arc covers all 4 compass points
            maxX = centerX + radius
            minY = centerY - radius
            minX = centerX - radius
            maxY = centerY + radius
            
            # We only have to calculate the min/max of p1 and p2 depending on which
            # quads A and B fall into
            if qA == qB:
                # If in the same quad, then we either cover all 4 compass points or none
                ang = Blender4CNC.Util2d.GetClockwiseAngleBetween(angA, angB)
                if ang < math.pi/2:
                    minY = min(p1[1], p2[1])
                    maxY = max(p1[1], p2[1])
                    minX = min(p1[0], p2[0])
                    maxX = max(p1[0], p2[0])
            elif qA == 0:
                maxY = max(p1[1], p2[1])
                if qB != 1:
                    minX = min(p1[0], p2[0])
                if qB == 3:
                    minY = min(p1[1], p2[1])
            elif qA == 1:
                minX = min(p1[0], p2[0])
                if qB != 2:
                    minY = min(p1[1], p2[1])
                if qB == 0:
                    maxX = max(p1[0], p2[0])
            elif qA == 2:
                minY = min(p1[1], p2[1])
                if qB != 3:
                    maxX = max(p1[0], p2[0])
                if qB == 1:
                    maxY = max(p1[1], p2[1])
            elif qA == 3:
                maxX = max(p1[0], p2[0])
                if qB != 0:
                    maxY = max(p1[1], p2[1])
                if qB == 2:
                    minX = min(p1[0], p2[0])
            return (minX, minY, maxX, maxY)

        #********************************************************************
        # Gets the x,y coordinates of a rectangle that encloses the curve 
        # from p1 to p2
        # Treats the curve just as a simple circle
        #********************************************************************
        def GetMinMaxCurveNonExact(self, p1, p2):        
            centerX = p2[2]
            centerY = p2[3]
            dx = centerX - p1[0]
            dy = centerY - p1[1]
            radius = math.sqrt(dx**2 + dy**2)

            # Assume the arc covers all 4 compass points
            maxX = centerX + radius
            minY = centerY - radius
            minX = centerX - radius
            maxY = centerY + radius
            return (minX, minY, maxX, maxY)
        
        #********************************************************************
        # Throws an exception if the shape of points and line segments is NOT 
        # a valid, REAL polytoxogon. Each segment can ONLY touch the previous 
        # segment at the start point and touch the next segment at the end 
        # point.
        #********************************************************************
        def IsValid(self):
            linesAndInts = self.GetIntersectionsBetweenAllLines(self.lines)
            linesAndIntsList = list(linesAndInts.items())
            linesAndIntsList.sort()
            # Since the lines were created from points, we KNOW that each segment should return 
            # exactly 2 intersections (with previous and next segments). If there is an intersection
            # with another segment, either in the middle or at an end point, or if there is an overlap
            # of infinite intersections, then there will be more than 2 intersections.
            # This will work for simple shapes of two line segments such as a circle or semi-circle.
            badSegments = [x for x in linesAndIntsList if len(x[1]) != 2]
            # It is also possible that we get two "intersections" such as a start intersection followed
            # by a infinite intersection
            # i.e.    1 :  [(0, (inf, ((2, 0), (1, 0)))), (2, (1, 0))]
            # Therefore we do also have to check for *ANY* inf intersections in the results
            #print("linesAndIntsList", linesAndIntsList)
            #print(linesAndIntsList[0][1][0][1][0])
            badSegmentsInf = [x for x in linesAndIntsList if x[1][0][1][0] == inf]
            p = None
            if len(badSegments) > 0:
                p = badSegments[0][1][0][1]
            elif len(badSegmentsInf) > 0:
                p = badSegmentsInf[0][1][0][1]
            if p != None:
                if p[0] == inf:
                    p = p[1][0]
                p = p[0:2]
                raise Blender4CNC.PolyException("Invalid Shape", p)
            # Also, check that the arcs make sense
            self.ArcsMakeSense() 
                    

        #********************************************************************
        def ImPolyIsClockwise(self):
            FEQ = Blender4CNC.FloatsAreEqual
            self.RemoveZeroLengthLines3()

            # There may be infinite overlapping lines or stubs which will complicate the function
            polys = self.SplitPolyOnInfiniteOverlaps()

            # Any "normal" polys must be tested clockwise; "overlap" stubs/segments can be "assumed"
            # clockwise on their own
            for poly in polys:
                if not poly.IsPureOverlapPoly():
                    if not poly.PolyIsClockwise():
                        return False
            return True                                                
        #********************************************************************
        #
        #********************************************************************
        def DetermineClockwise180(self, lineA, lineB):
            PI = math.pi
            # We have done a 180, determine what type of turn it is +180 or -180
            # Assuming that this function is only called on valid polys, we can never have 
            # two straight lines
            if (len(lineA[1]) == 2) and (lineB[1][4] == 1):
                return -PI
            elif (len(lineB[1]) == 2) and (lineA[1][4] == 1):
                return -PI
            elif (len(lineA[1]) > 2) and (len(lineB[1]) > 2):
                # We have two curves
                A_is_CW = (lineA[1][4] == 1)
                B_is_CW = (lineB[1][4] == 1)
                if A_is_CW and B_is_CW:
                    return -PI
                elif A_is_CW != B_is_CW:
                    (a,b) = lineA
                    (c,d) = lineB
                    radiusASqr = (b[0] - b[2])**2 + (b[1] - b[3])**2
                    radiusBSqr = (d[0] - d[2])**2 + (d[1] - d[3])**2
                    if not A_is_CW:
                        if radiusASqr > radiusBSqr:
                            return -PI
                    else:
                        if radiusASqr < radiusBSqr:
                            return -PI
            return PI
        def PolyIsClockwise(self):
            # Get the start, end vectors for all segments
            startVectors = [self.GetSegVectorAtPoint(line,line[0]) for line in self.lines]
            endVectors = [self.GetSegVectorAtPoint(line,line[1]) for line in self.lines]
            # Get all angles between end/start vectors
            angles = []
            PI = math.pi
            TWO_PI = 2*math.pi
            FEQ = Blender4CNC.FloatsAreEqual
            for i in range(0,len(startVectors)):
                angle = self.GetClockwiseAngleBetweenVectors(endVectors[i-1], startVectors[i])
                if angle > PI:
                    angle = angle - TWO_PI
                if FEQ(angle, PI):
                    angle = self.DetermineClockwise180(self.lines[i-1], self.lines[i])
                angles.append(angle)
            # Get angles of all curves
            curves = [x for x in self.lines if len(x[1]) > 2]
            curveAngles = [self.GetCurveAngle(x) for x in curves]
            # To be clockwise, the sum of all angles and curve angles should be 2pi
            total = sum(angles) + sum(curveAngles)
            tf = FEQ(total, TWO_PI)
            return tf
        #********************************************************************
        # Returns a new Polytoxogon in which all the line segments have been 
        # reversed.
        #********************************************************************
        def ReverseLineDirections(self):
            if len(self.points) == 0:
                return Blender4CNC.Polytoxogon([])
            
            l = self.points
            l2 = []
            for i in range(0,len(l)):
                p1 = l[i]
                p2 = l[(i+1) % len(l)]
                if self.PointIsStraight(p2):
                    l2.append((p1[0], p1[1]))
                else:
                    l2.append((p1[0], p1[1], p2[2], p2[3], -p2[4]))
            temp = l2.pop(0)
            l2.reverse()
            l2 = [temp] + l2
            
            return Blender4CNC.Polytoxogon(l2)

        #********************************************************************
        # Returns all the parallel line segments (just takes the simple 
        # approach) of the poly
        #********************************************************************
        def GetSimpleParallelSides(self, dist):
            # Get the lines that are parallel to the sides 
            newLines = []
            for line in self.lines:
                if self.PointIsStraight(line[1]):
                    newLine1 = self.GetParallelLine((line[0], line[1]), dist)
                else:
                    newLine1 = self.GetParallelCurve((line[0], line[1]), dist)
                newLines.append(newLine1)
            return newLines

        #********************************************************************
        # Given 2 lines segments in a list of parallel sides, determines
        # if there should be a connecting curve to connect them
        #********************************************************************
        def ParallelSidesNeedJoinCurve(self, line1, line2, dist):
            
            #if this is a 
            v = self.GetSegVectorAtPoint((line1[0], line1[1]), line1[1])
            v = (-v[0], -v[1], -v[2])
                
            segVec1 = v
            segVec2 = self.GetSegVectorAtPoint((line2[0], line2[1]), line1[1])
            segVec2 = segVec2
            angle = self.GetClockwiseAngleBetweenSegVectors(segVec2, segVec1)
            return (not Blender4CNC.FloatsAreEqual(angle,pi)) and (angle > pi)
        
        #********************************************************************
        # Given 2 lines segments in a list of parallel sides, adds
        # a connecting curve to connect them
        #********************************************************************
        def ParallelSidesAddJoinCurve(self, line1, line2, newLine1, newLine2, dist):
            p1 = newLine1[1]
            (cX, cY) = (line1[1][0], line1[1][1])
            if newLine2 == None:
                if self.PointIsStraight(line2[1]):
                    newLine2 = self.GetParallelLine(line2, dist)
                else:
                    newLine2 = self.GetParallelCurve(line2, dist)
            CW = -1
            p2 = (newLine2[0][0], newLine2[0][1], cX, cY, CW)
            return (p1, p2)

        #********************************************************************
        # Given the line segments of a polygon, returns all the parallel line
        # segments 
        #********************************************************************
        def GetParallelSides(self, dist):

            newLinesZ = self.RemoveZeroLengthLines(self.lines)
            if len(newLinesZ) != len(self.lines):
                points = [x[1] for x in newLinesZ]
                points = [points[-1]] + points[0:-1]
                polyZ = Blender4CNC.Polytoxogon(points)
                lines = polyZ.lines
                parLines = polyZ.GetSimpleParallelSides(dist)
            else:
                lines = self.lines
                parLines = self.GetSimpleParallelSides(dist)
               
#            parLines = self.GetSimpleParallelSides(dist)
            parLines = [(x[0], x[1]) for x in parLines]

            # Check if we have any concave curves that shrank to a single point, because if we do,
            # it means that we have a curve that is too small for the bit diameter (the larger bit
            # will "bump" across the arc instead of rolling around the arc
            for i,line in enumerate(parLines):
                if self.PointsAreEqual(line[0], line[1]):
                    curve = lines[i] # The original start, end points
                    #if self.PointsAreEqual(curve[0], curve[1]):
                        # The original line starts/ends at same point - circle.
                        # Skip this!
                        # This is unreachable code now?
                    #    continue
                    center = line[0]
                    p1 = (curve[0][0], curve[0][1])
                    p2 = (curve[1][0], curve[1][1])
                    pHalf = (p2[0] - p1[0], p2[1] - p1[1])
                    pHalf = (pHalf[0]/2, pHalf[1]/2)
                    len1sqrd = pHalf[0]**2 + pHalf[1]**2
                    pHalf = (p1[0] + pHalf[0], p1[1] + pHalf[1])
# Assuming CW for now
                    v1 = (p1[0] - center[0], p1[1] - center[1])
                    v2 = (p2[0] - center[0], p2[1] - center[1])
                    a1 = atan2(v1[1], v1[0])
                    a2 = atan2(v2[1], v2[0])
                    ang = Blender4CNC.Util2d.GetClockwiseAngleBetween(a1, a2)
                    if ang < math.pi:
                        # Direction vector is from pHalf to center
                        vv = (center[0] - pHalf[0], center[1] - pHalf[1])
                    else:
                        # Direction vector is from center to pHalf
                        vv = (pHalf[0] - center[0], pHalf[1] - center[1])
                    vvLen = math.sqrt(vv[0]**2 + vv[1]**2)
                    if Blender4CNC.FloatsAreEqual(vvLen, 0.0):
                        # This means that the center of the curve is exactly on pHalf
                        # or that we have an exact semicircle, the direction is taken as right 
                        # angle of p1->p2 (which is same as v2 direction)
                        vv = (v2[1], -v2[0])
                        vvLen = math.sqrt(vv[0]**2 + vv[1]**2)
                    vv = (vv[0]/vvLen, vv[1]/vvLen)
                    len2 = math.sqrt(dist**2 - len1sqrd)
                    vv = (vv[0]*len2, vv[1]*len2)
                    newCenter = (pHalf[0] + vv[0], pHalf[1] + vv[1])
                    parLines[i] = (newCenter, newCenter)

            newLines = []
            newLines2 = [(x[0], x[1]) for x in lines]
            for i in range(0,len(lines)):
                nexti = (i + 1) % len(lines)
                newLines.append((parLines[i][0], parLines[i][1]))
                if self.ParallelSidesNeedJoinCurve(newLines2[i],newLines2[nexti], dist):
                    curve = self.ParallelSidesAddJoinCurve((lines[i][0], lines[i][1]), (lines[nexti][0], lines[nexti][1]), (parLines[i][0], parLines[i][1]),(parLines[nexti][0], parLines[nexti][1]), dist)
                    curve = (curve[0], curve[1])
                    newLines.append((curve[0], curve[1]))
            newLines = self.RemoveZeroLengthLines(newLines)
            return newLines

        #********************************************************************
        # Given two segVectors (special 3 values) - returns the clockwise
        # angle beteween them as we rotate from segVec1 to segVec2
        #********************************************************************
        def GetClockwiseAngleBetweenSegVectors(self, segVec1, segVec2):
            ang = self.GetClockwiseAngleBetweenVectors(segVec1, segVec2)
            
            # If the simple vectors are equal, look at z component
            if Blender4CNC.FloatsAreEqual(ang, 0):
                if Blender4CNC.FloatsAreEqual(segVec2[2], segVec1[2]):
                    # A Stub (straight or curved)
                    # THIS WORKS FOR EXPAND BUT NOT TESTED WITH SHRINK!!!!!!!!!!!!!!!!!!!
                    ang = 2*pi
                elif segVec2[2] > segVec1[2]:
                    ang = 2*pi
                else:
                    ang = 0
            return ang

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A class that can parse a GCode file and create a curve object representing the tool path
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS GCodePathViewer
    class GCodePathViewer:
        
        def __init__(self):
            pass

        #**************************************************************************
        # Visualize a GCode file by producing a curve object that represents the 
        # tool path. The GCode file is specified in "filename", the resultant
        # curve object will be called "name" and will have "pathMat" material
        # applied to it
        # 'scale' is used to scale all the coordinates of the path. This is due
        # to how Blender operates with units - if a GCode path is in IMPERIAL, we
        # must scale all the coordinates because Blender is essentially metric.
        # Projects with "METRIC" or "NONE" for units can use a scale of 1.
        #**************************************************************************
        def VisualizeGCodePath(self, name, pathMat, name2, delOld, bevelDepth, scale):
            if delOld:        
                self.RemoveObject(name)

            filename = name2

            g = Blender4CNC.GCodeMachine()

    # Test files from ncFiles folder in LinuxCNC
    #
    # /home/d/Downloads/linuxcnc-master/bin/3D_Chips.ngc
    #
    # OK    3D_Chips, b-index, cds, comp311_2, comp311, comp-g1, gmoccapy_2_tools_with_cutter_radius_compensation, plasmatest,
    #       skeleton, gridprobe, flowsnake, daisy, offsets
    # (modified one line in gridprobe.ngc for explicitly handling expressions)
    #
    # FAILING XYZ PLANE                 3dtest, comp, lathecomp, lathe_pawn, tort
    # NURBS?                            butterfly, systems
    # NEED TOOL TABLE FOR RS274?        lathe-g76
    # G76 NOT IMPLEMENTED (LATHE)       g76
    # G70/G72 NOT IMPLEMENTED (LATHE)   lathe_g70_71_demo, lathe_g7x_face_boring, lathe_g7x_quadrants
    # G33... NOT IMPLEMENTED (LATHE)    threading
    # '^' CHARACTER                     hole-circle, polar, spiral
    # IS A SUBROUTINE FILE?             m250, m61demo, m6demo, m6remap, touchoff
    # HELICAL ARCS                      mmount

    # ??? INFINITE flowsnake, daisy
#            g.go("/home/d/Downloads/linuxcnc-master/nc_files/skeleton.ngc")
            g.go(filename)
#            print("g.output=", g.output)
            if (g.machine.units == "IMPERIAL") and (bpy.context.scene.unit_settings.system != "IMPERIAL"):
                raise Exception("GCode is imperial, this project is not in imperial units!")
            if (g.machine.units == "METRIC") and (bpy.context.scene.unit_settings.system != "METRIC"):
                raise Exception("GCode is metric, this project is not in metric units!")

            content = g.output

            words2Ignore = ["USE_LENGTH_UNITS", "SET_G5X_OFFSET", "SET_G92_OFFSET", "SET_XY_ROTATION", "SET_FEED_REFERENCE"]
            words2Ignore += ["ON_RESET", "COMMENT", "SET_MOTION_CONTROL_MODE", "SET_NAIVECAM_TOLERANCE", "SELECT_TOOL"]
            words2Ignore += ["START_CHANGE", "STOP_SPINDLE_TURNING", "CHANGE_TOOL", "FLOOD_ON", "SET_SPINDLE_SPEED"]
            words2Ignore += ["START_SPINDLE_CLOCKWISE", "SET_FEED_RATE", "MIST_OFF", "FLOOD_OFF", "SET_FEED_MODE"]
            words2Ignore += ["SET_FEED_RATE", "SET_SPINDLE_MODE", "PROGRAM_END", "USE_TOOL_LENGTH_OFFSET", "DWELL"]
            words2Ignore += ["MESSAGE", "FINISH", "OPTIONAL_PROGRAM_STOP", "MIST_ON", "TURN_PROBE_ON", "TURN_PROBE_OFF"]
            words2Ignore += ["START_SPEED_FEED_SYNC", "RIGID_TAP", "STOP_SPEED_FEED_SYNCH", "CHANGE_TOOL_NUMBER", "PALLET_SHUTTLE"]
            words2Ignore += ["PROGRAM_STOP", "START_SPINDLE_COUNTERCLOCKWISE"]

            coords = [(0,0,0,1)]    
            CANON_PLANE = "CANON_PLANE_XY"
            count = 0
            for line in content:
                word = line[0]

                if word in ["STRAIGHT_FEED", "STRAIGHT_TRAVERSE"]:
                    coords.append((line[1], line[2], line[3], 1))
                elif word in ["STRAIGHT_PROBE"]:
                    words = self.Get6FloatsAsStrings(line)
                    f = [float(x) for x in words]
                    coords.append((f[0], f[1], f[2], 1))
                elif word == "ARC_FEED":

                    endX = line[1]
                    endY = line[2]
                    centerX = line[3]
                    centerY = line[4]
                    CW = line[5]

                    (lastX, lastY, lastZ, lastW) = coords[-1]
                    if CANON_PLANE == "CANON_PLANE_XY":
                        p1 = Vector((lastX, lastY))
                        p2 = Vector((endX, endY))
                        center = Vector((centerX, centerY))
                        if CW == -1:
                            wantCW = True
                        else:
                            wantCW = False
                    elif CANON_PLANE == "CANON_PLANE_XZ":
                        # Z is 1st axis, X is 2nd axis ?
                        p1 = Vector((lastX, lastZ))
                        p2 = Vector((endY, endX))
                        center = Vector((centerY, centerX))
                        # Clockwise is chosen as looking "down" the +ve 3rd axis
                        if CW == -1:
                            wantCW = False
                        else:
                            wantCW = True
                    elif CANON_PLANE == "CANON_PLANE_YZ":
                        p1 = Vector((lastY, lastZ))
                        p2 = Vector((endX, endY))
                        center = Vector((centerX, centerY))
                        if CW == -1:
                            wantCW = True
                        else:
                            wantCW = False
                        
                    #print("starting at p1[0], p1[1]=", p1[0], p1[1])
                    #print("ending at p2[0], p1[1]=", p2[0], p2[1])
                    #print("center at center[0], center[1]=", center[0], center[1])
                    v1 = p1 - center
                    v2 = p2 - center
                    #print("v1[0], v1[1]=", v1[0], v1[1])
                    radius = v1.length
                    a1 = atan2(v1[1], v1[0])
                    a2 = atan2(v2[1], v2[0])
                    ang = Blender4CNC.Util2d.GetClockwiseAngleBetween(a1, a2)
                    #print("a1, a2, clockwise ang=", a1, a2, ang)
                    if not wantCW: 
                        ang = 2*pi - ang
                        
                    #print("a1, a2, ang=", a1, a2, ang)

                    # Must go from last to end in 10deg steps
                    radian = pi / 180
                    radian *= 10

                    if Blender4CNC.FloatsAreEqual(ang, 0):
                        ang = 2 * pi
                    if wantCW: 
                        curAng = a1 - radian
                    else:
                        curAng = a1 + radian
                    #print("a1, curAng, ang, radius=", a1, curAng, ang, radius)
                    while ang > radian:
                        if CANON_PLANE == "CANON_PLANE_XY":
                            x = cos(curAng) * radius
                            y = sin(curAng) * radius
                            coords.append((x+center[0],y+center[1],lastZ,1))
                        elif CANON_PLANE == "CANON_PLANE_XZ":
                            # Z is 1st axis, X is 2nd axis ?
                            x = cos(curAng) * radius
                            z = sin(curAng) * radius
                            coords.append((x+center[0],lastY,z+center[1],1))
                        elif CANON_PLANE == "CANON_PLANE_YZ":
                            y = cos(curAng) * radius
                            z = sin(curAng) * radius
                            coords.append((lastX,y+centerY,z+centerY,1))
                        ang -= radian
                        if wantCW: 
                            curAng = curAng - radian
                        else:
                            curAng = curAng + radian
                        #print("curAng, ang=", curAng, ang)
                        #print(coords[-1])
                    if CANON_PLANE == "CANON_PLANE_XY":
                        coords.append((p2[0],p2[1],lastZ,1))
                    elif CANON_PLANE == "CANON_PLANE_XZ":
                        coords.append((p2[0],lastY,p2[1],1))
                    elif CANON_PLANE == "CANON_PLANE_YZ":
                        coords.append((endX,endY,lastZ,1))
                    #print("ending at ", coords[-1])
                elif word == "SELECT_PLANE":
                    # We have to keep track of which plane we are in
                    CANON_PLANE = words[1].split(")")[0]
                elif word in words2Ignore:
                    pass
                elif word == "NURBS_FEED":
                    pass
                else:
                    print(line) 
                    raise Exception("UNKNOWN FUNCTION IN VisualizeGCodePath")

            # If the GCode is imperial and this is an imperial project, must convert numbers to                     
            # display project properly
            if (g.machine.units == "METRIC") and (bpy.context.scene.unit_settings.system == "METRIC"):
                scale = 0.001
            if (bpy.context.scene.unit_settings.system == "NONE") and (g.machine.units == "IMPERIAL"):
                m = 1
            elif (bpy.context.scene.unit_settings.system == "NONE") and (g.machine.units == "METRIC"):
                m = 1
            else:
                #print("VisualizeGCodePath scale =", scale)
                m = scale
            #print("VisualizeGCodePath m =", m)
            for i in range(0,len(coords)):
                coords[i] = (coords[i][0] * m, coords[i][1] * m, coords[i][2] * m, 1)
                
#            print("VisualizeGCodePath coords =", coords)
#            print("VisualizeGCodePath coords[0] =", coords[0])
#            print("VisualizeGCodePath coords[1] =", coords[1])
#            print("VisualizeGCodePath coords[2] =", coords[2])
#            print("VisualizeGCodePath coords[3] =", coords[3])
            self.CreatePath(name, pathMat, coords, bevelDepth)
            return coords

        #**************************************************************************
        # Create the curve object from the coordinates and apply a material
        #**************************************************************************
        def CreatePath(self, name, pathMat, coords, bevelDepth):
            # create the Curve Datablock
            curveData = bpy.data.curves.new(name, type='CURVE')
            curveData.dimensions = '3D'
            curveData.resolution_u = 2

            # map coords to spline
            polyline = curveData.splines.new('POLY')
            polyline.points.add(len(coords))
            for i, coord in enumerate(coords):
                (x,y,z,w) = coord
                polyline.points[i].co = (x, y, z, 1)

            # create Object
            curveOB = bpy.data.objects.new(name, curveData)
            curveOB.data.bevel_depth = bevelDepth
            curveOB.data.fill_mode = 'FULL'
            curveOB.data.materials.append(pathMat) # Set the material
            
            scn = bpy.context.scene
            scn.collection.objects.link(curveOB)

        #**************************************************************************
        # Given a line like (0.000, 1.000 ..... ) will get the 1st 6 numbers
        # and return them as a list of strings
        #**************************************************************************
        def Get6FloatsAsStrings(self, line2):
            words = line2.split("(")
            words.pop(0)
            line = " ".join(words)
            words = line.split(")")
            line = words[0]
            words = line.split(" ")
            line = "".join(words)
            words = line.split(",")
            return words

        #**************************************************************************
        # Remove the object if it already exists
        #**************************************************************************
        def RemoveObject(self, name):
            objs = bpy.data.objects
            curves = bpy.data.curves
            coll_objs = bpy.context.scene.collection.objects
            if name in objs.keys():
                obj = objs[name]
                if name in coll_objs.keys():
                    coll_objs.unlink(obj)
                if name in curves.keys():
                    curve = curves[name]
                    curves.remove(curve)
                if name in objs.keys():
                    objs.remove(obj)

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Structure class to handle parameters (project, job/global, and local)
    # Each line SHOULD be in the format: <string> = <number/string/bool> (i.e. X=0)
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS Parameters
    class Parameters:

        def __init__(self):
            self.REAL_EXPR = "([+-]?(\d+\.\d+|\.\d+|\d+\.|\d+))"
            self.realNumberProg = re.compile("^" + self.REAL_EXPR)
            self.projectParams = {}
            self.localParams = {}
            self.collectionParams = {}
            self.globalParams = {}

        #*************************************************************************
        # Return a list of the children of an object
        #*************************************************************************
        def GetChildren(self, ob):
            return [ob_child for ob_child in bpy.data.objects if ob_child.parent == ob]

        #*************************************************************************
        # Find an object by name
        #*************************************************************************
        def ReturnObjectByName (self, passedName= ""):
            return bpy.data.objects[passedName]

        #*************************************************************************
        # Get the Global/Job Parameters
        #*************************************************************************
        def SetGlobalJobParameters(self):
            self.globalParams = {}
            name = "JobParameters"
            if name in bpy.data.objects.keys():
                ob = self.ReturnObjectByName(name)
                if ob.type == 'FONT':
                    par = ob.data.body.splitlines()
                    self.globalParams = self.GetParameters(par)
            if len(self.globalParams.keys()) == 0:
                raise Exception("Cannot find Job Parameters?", (0,0))
            return self.globalParams

        #*************************************************************************
        # Check all fields are present in Project Parameters
        #*************************************************************************
        def CheckProjectParameters(self):
            for s in ["Version", "MsgHeight", "PathBevelDepth", "MsgZOffset", "PathZOffset"]:
                if s not in self.projectParams.keys():
                    raise Exception("Project Parameters does not contain %s parameter!" %s, (0,0))

        #*************************************************************************
        # Get the Project Parameters
        #*************************************************************************
        def SetProjectParameters(self):
            self.projectParams = {}
            name = "ProjectParameters"
            if name in bpy.data.objects.keys():
                ob = self.ReturnObjectByName(name)
                if ob.type == 'FONT':
                    par = ob.data.body.splitlines()
                    self.projectParams = self.GetParameters(par)
            if len(self.projectParams.keys()) == 0:
                raise Exception("Cannot find Project Parameters?", (0,0))
            return self.projectParams

        #*************************************************************************
        # If the current operation (given by 'oName') has parameters, read them
        # and set them into the 'localParams' variable
        #*************************************************************************
        def SetLocalParameters(self, oName):
            obj = self.ReturnObjectByName(oName)
            children = self.GetChildren(obj)   
            listOfObjs = [ob for ob in children if ob and (ob.type == 'FONT') and (ob.name[0:10] == "Parameters")]
            listOfParams = []
            if len(listOfObjs) > 0:
                listOfParams = listOfObjs[0].data.body.splitlines()
            self.localParams = self.GetParameters(listOfParams)
            return self.localParams

        #*************************************************************************
        # If the current collection (given by 'oName') has parameters (a child
        # object called 'Parameters', read them and set them into the 'collectionParams'
        # variable
        #*************************************************************************
        def SetCollectionParameters(self, oName) :
            # Loop through this collection looking for a parameter
            listOfObjs = [ob for ob in oName.objects if ob and (ob.type == 'FONT') and (ob.name[0:15] == "LayerParameters")]
#            print("SetCollectionParameters listOfObjs=", listOfObjs)
            listOfParams = []
            if len(listOfObjs) > 0:
                listOfParams = listOfObjs[0].data.body.splitlines()
#            print("SetCollectionParameters listOfParams=", listOfParams)
            self.collectionParams = self.GetParameters(listOfParams)
#            print("SetCollectionParameters self.collectionParams=", self.collectionParams)
            return self.collectionParams

        #*************************************************************************
        # Generic function called by GetLocalParameters and GetLayerParameters
        # Each line SHOULD be in the format: <string> = <number> (i.e. X=0)
        #*************************************************************************
        def GetParameters(self, l):
            localParams = {}
            VARIABLE = "\s*(\w+)\s*"
            for line in l:
                # Look for numbers
                m = re.match(VARIABLE + "=\s*([+-]?\d+(?:\.\d+)?)\s*", line)
                if m:
                    localParams[m.group(1)] = float(m.group(2))
                else:
                    # Look for booleans
                    m = re.match(VARIABLE + "=\s*(True|False)\s*", line)
                    if m:
                        localParams[m.group(1)] = bool(m.group(2))
                    else:
                        # Look for strings
                        m = re.match(VARIABLE + "=\s*\"(\w*)\"\s*", line)
                        if m:
                            localParams[m.group(1)] = m.group(2)
            return localParams

        #*************************************************************************
        # Look for a parameter in the local parameters first and return it as a
        # float, if not in the local parameters then get it from the global
        # parameters
        #*************************************************************************
        def LocalOrGlobal(self, s):
            if s in self.localParams:
                return self.localParams[s]
            if s in self.collectionParams:
                return self.collectionParams[s]
            return self.globalParams[s]
        def Global(self, s):
            return self.globalParams[s]
        def ProjectParameter(self, s):
            return self.projectParams[s]
        def HasGlobalParameter(self, s):
            return s in self.globalParams.keys()
        def HasCollectionParameter(self, s):
            return s in self.collectionParams.keys()
        def CollectionParameter(self, s):
            return self.collectionParams[s]
                
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Class to handle the creation of operations like pocket, path, hole...
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS CreateOpsClass
    class CreateOpsClass:

        def __init__(self, blender4CNCParent):
            self.parent = blender4CNCParent

        def CreatePocketPath(self, verts, edges, faces, name, cX = 0, cY = 0):
            bpy.ops.object.select_all(action='DESELECT')

            mesh_data = bpy.data.meshes.new("pocket_mesh_data")
            
            mesh_data.from_pydata(verts, edges, faces)
            mesh_data.update()

            obj = bpy.data.objects.new(name, mesh_data)

            scene = bpy.context.scene
            
            # Add to active collection
            bpy.context.view_layer.active_layer_collection.collection.objects.link(obj)
            obj.select_set(state=True)

            # unselect all vertices, select just the first point and the "top" point
            # Find the indexes of the two selected vertices
            verts = [vertex for vertex in obj.data.vertices]
            indexes = []
            for i in range(0,len(verts)):
                verts[i].select = False
                if Blender4CNC.FloatsAreEqual(verts[i].co.x, cX) and Blender4CNC.FloatsAreEqual(verts[i].co.y, cY):
                    verts[i].select = True
                    indexes += [i]

            # Find the selected edge and set bevel_weight (start edge)
#            obj.data.use_customdata_edge_bevel = True
            edges = [e for e in obj.data.edges]
            edges2 = [e for e in edges if indexes[0] in e.vertices]
            edges2 = [e for e in edges2 if indexes[1] in e.vertices]
            edge = edges2[0]
            edge.bevel_weight = 1

            # Select JUST the new object AND make it active
            bpy.ops.object.select_all(action='DESELECT')
            obj.select_set(state=True)
            bpy.context.view_layer.objects.active = obj

            return obj

        def SetPocketMaterial(self, obj):
            # Get material for Pockets if it exists
            if "Color4Pockets" in bpy.data.materials.keys():
                mat = bpy.data.materials["Color4Pockets"]
                obj.data.materials.append(mat)

        #*************************************************************************
        # Create CW Pocket
        #*************************************************************************
        def CreateCWPocket(self):
            (z,SZ) = Blender4CNC.GetzSZ()
            verts = [(0,0,0), (0,SZ,0), (SZ,SZ,0), (SZ,0,0), (0,0,SZ)]
            edges = [[0,4], [4,1]]
            faces = [[0,1,2,3]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.Pocket.X")
            obj.location = (0,0,z)
            self.SetPocketMaterial(obj)
        
        #*************************************************************************
        # Create Tenon
        #*************************************************************************
        def CreateTenon(self):
            # Need to check that one pocket is selected
            if len(bpy.context.selected_objects) == 0:
                raise Exception("Nothing selected!", (0,0))
                    
            if len(bpy.context.selected_objects) != 1:
                raise Exception("Too many objects selected!", (0,0))

            ob = bpy.context.selected_objects[0]
            if ob.name[4:10] != "Pocket":
                raise Exception("Please select a pocket only!", (0,0))
            
            (z,SZ) = Blender4CNC.GetzSZ()
            z *= 2
            verts = [(0,0,0), (0,SZ,0), (SZ,SZ,0), (SZ,0,0), (0,0,SZ)]
            edges = [[0,4], [4,1]]
            faces = [[0,1,2,3]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.Tenon.X")
            obj.location = (ob.location.x,ob.location.y,z)

            # Parent tenon to pocket        
            for ob2 in bpy.data.objects:
                ob2.select_set(state=False)

            obj.select_set(state=True)
            ob.select_set(state=True)
            # Make the parent object active
            bpy.context.view_layer.objects.active = ob
            bpy.ops.object.parent_set(type='OBJECT', keep_transform=False)
        
            # Unselect the parent, then activate the child (tenon)
            ob.select_set(state=False)
            bpy.context.view_layer.objects.active = obj
            
            # Get material for Tenon if it exists
            if "Color4Blank" in bpy.data.materials.keys():
                mat = bpy.data.materials["Color4Blank"]
                obj.data.materials.append(mat)

        #*************************************************************************
        # Create CCW Pocket
        #*************************************************************************
        def CreateCCWPocket(self):
            (z,SZ) = Blender4CNC.GetzSZ()
            verts = [(0,0,0), (0,SZ,0), (SZ,SZ,0), (SZ,0,0), (0,0,SZ)]
            edges = [[0,4], [4,3]]
            faces = [[0,1,2,3]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.Pocket.X")
            obj.location = (0,0,z)
            self.SetPocketMaterial(obj)

        #*************************************************************************
        # Create Closed Path
        #*************************************************************************
        def CreateClosedPath(self):
            (z,SZ) = Blender4CNC.GetzSZ()
            verts = [(0,0,0), (0,SZ,0), (SZ,SZ,0), (SZ,0,0), (0,0,SZ)]
            edges = [[0,1], [1,2], [2,3], [3,0], [0,4], [4,1]]
            faces = [[0,4,1]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.Path.X")
            obj.location = (0,0,z)

        #*************************************************************************
        # Create Open Path
        #*************************************************************************
        def CreateOpenPath(self):
            (z,SZ) = Blender4CNC.GetzSZ()
            verts = [(0,0,0), (SZ,0,0), (SZ,SZ,0), (2*SZ,SZ,0), (0,0,SZ)]
            edges = [[0,1], [1,2], [2,3], [0,4], [4,1]]
            faces = [[0,4,1]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.Path.X")
            obj.location = (0,0,z)

        def FindVerticeIndex(self, obj, cX, cY):
            verts = [vertex for vertex in obj.data.vertices]
            for i in range(0,len(verts)):
                if Blender4CNC.FloatsAreEqual(verts[i].co.x, cX) and Blender4CNC.FloatsAreEqual(verts[i].co.y, cY):
                    return i
            
        def MakeRadiusForIndices(self, obj, ndx1, ndx2):
            # Find the selected edge and set bevel_weight (start edge)
#            obj.data.use_customdata_edge_bevel = True
            edges = [e for e in obj.data.edges]
            edges2 = [e for e in edges if ndx1 in e.vertices]
            edges2 = [e for e in edges2 if ndx2 in e.vertices]
            edge = edges2[0]
            edge.use_seam = True
            return obj

        def MakeCurveForIndices(self, obj, ndx1, ndx2):
            #print("MakeCurveForIndices ndx1, ndx2=", ndx1, ndx2)
            # Find the selected edge and set bevel_weight (start edge)

            # I do not know why this happens, but sometimes, the first time a curve segment is made on a mesh,
            # the 0th edge gets marked instead of the intended, by sheer chance, if you toggle the first edge
            # on/off or off/on, then you can successfully set the one you want. Very Weird! It doesn't *seem*
            # like it is somehow holding a pointer to old mesh data...is there a bug in Blender?
            obj.data.edges[0].use_freestyle_mark = not obj.data.edges[0].use_freestyle_mark
            obj.data.edges[0].use_freestyle_mark = not obj.data.edges[0].use_freestyle_mark

            edges = [e for e in obj.data.edges]
            edges2 = [e for e in edges if ndx1 in e.vertices]
            edges2 = [e for e in edges2 if ndx2 in e.vertices]
            edge = edges2[0]
            edge.use_freestyle_mark = True
            return obj
        
        def SubCreateCircle(self, isPath):
            if bpy.context.scene.unit_settings.system == "METRIC":
                m = 0.05
                z = 0.001
                zStart = 0.05
            else:
                m = 1 / Blender4CNC.METERS_TO_INCHES # one inch
                z = 0.01 * m
                zStart = 1 / Blender4CNC.METERS_TO_INCHES
            rad = math.pi
            numSteps = 16
            step = rad/numSteps
            verts = []
            while (rad >= -math.pi) and not Blender4CNC.FloatsAreEqual(rad, -math.pi):
                x = math.cos(rad)
                y = math.sin(rad)
                verts.append((x * m, y * m, 0))
                rad -= step
            point0 = copy.copy(verts[0])
            point1 = copy.copy(verts[1])
            point2 = copy.copy(verts[2])
            pointnextlast = copy.copy(verts[-1])
            pointlast = copy.copy(verts[0])
            verts.append((-m,0,zStart))
            verts.append((0,0,0))
            
            edges = []
            for i in range(0,numSteps*2-1):
                edges.append([i,i+1])
            edges.append([numSteps*2-1,0])
                
            edges.append([0,numSteps*2])
            edges.append([1,numSteps*2])
            edges.append([2,numSteps*2+1])

            if isPath:
                faces = [[0,1,numSteps*2]]
                obj = self.CreatePocketPath(verts, edges, faces, "001.Path.Circle", -1 * m, 0)
            else:
                faces = []
                for i in range(0,numSteps*2):
                    faces.append(i)
                faces = [faces]
                obj = self.CreatePocketPath(verts, edges, faces, "001.Pocket.Circle", -1 * m, 0)

            ndx1 = self.FindVerticeIndex(obj, point0[0], point0[1])
            ndx2 = self.FindVerticeIndex(obj, point1[0], point1[1])
            self.MakeCurveForIndices(obj, ndx1, ndx2)
            ndx1 = self.FindVerticeIndex(obj, pointnextlast[0], pointnextlast[1])
            ndx2 = self.FindVerticeIndex(obj, pointlast[0], pointlast[1])
            self.MakeCurveForIndices(obj, ndx1, ndx2)
            ndx1 = self.FindVerticeIndex(obj, point2[0], point2[1])
            ndx2 = self.FindVerticeIndex(obj, 0, 0)
            self.MakeRadiusForIndices(obj, ndx1, ndx2)
            obj.location = (0,0,z)
            return obj

        #*************************************************************************
        # Create Circle Path
        #*************************************************************************
        def CreateCirclePath(self):
            self.SubCreateCircle(True)

        #*************************************************************************
        # Create Circle Pocket
        #*************************************************************************
        def CreateCirclePocket(self):
            obj = self.SubCreateCircle(False)
            self.SetPocketMaterial(obj)

        #*************************************************************************
        # Create Hole
        #*************************************************************************
        def CreateHole(self):
            (z,SZ) = Blender4CNC.GetzSZ()
            verts = [(0,0,0), (0,0,SZ), (0,SZ/2,SZ/2)]
            edges = []
            faces = [[0,1,2]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.Hole.X")
            obj.location = (0,0,z)

        #*************************************************************************
        # Create DrillPath
        #*************************************************************************
        def CreateDrillPath(self):
            (z,SZ) = Blender4CNC.GetzSZ()
            verts = [(0,0,0), (0,SZ,0), (SZ,SZ,0), (SZ,0,0), (0,0,SZ)]
            edges = [[0,1], [1,2], [2,3], [0,4], [4,1]]
            faces = [[0,4,1]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.DrillPath.X")
            obj.location = (0,0,z)

        #*************************************************************************
        # Create Arc Path
        #*************************************************************************
        def CreateArcPath(self):
            rad = math.pi
            numSteps = 16
            step = rad/numSteps
            verts = []
            if bpy.context.scene.unit_settings.system == "METRIC":
                m = 0.05
                z = 0.001
                zStart = 0.05
            else:
                m = 1 / Blender4CNC.METERS_TO_INCHES # one inch
                z = 0.01 * m
                zStart = 1 / Blender4CNC.METERS_TO_INCHES
            while (rad >= 0) or Blender4CNC.FloatsAreEqual(rad, 0):
                x = math.cos(rad)
                y = math.sin(rad)
                verts.append((x * m, y * m, 0))
                rad -= step
            point0 = copy.copy(verts[0])
            point1 = copy.copy(verts[1])
            point2 = copy.copy(verts[2])
            pointnextlast = copy.copy(verts[-2])
            pointlast = copy.copy(verts[-1])
            verts.append((-m,0,zStart)) # Add the top of the start point
            verts.append((0,0,0))
            
            edges = []
            for i in range(0,numSteps):
                edges.append([i,i+1])
            edges.append([0,numSteps+1])
            edges.append([1,numSteps+1])
            edges.append([2,numSteps+2])

            faces = [[0,1,numSteps+1]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.Path.Arc", -1 * m, 0)
            ndx1 = self.FindVerticeIndex(obj, point0[0], point0[1])
            ndx2 = self.FindVerticeIndex(obj, point1[0], point1[1])
            self.MakeCurveForIndices(obj, ndx1, ndx2)
            ndx1 = self.FindVerticeIndex(obj, pointnextlast[0], pointnextlast[1])
            ndx2 = self.FindVerticeIndex(obj, pointlast[0], pointlast[1])
            self.MakeCurveForIndices(obj, ndx1, ndx2)
            ndx1 = self.FindVerticeIndex(obj, point2[0], point2[1])
            ndx2 = self.FindVerticeIndex(obj, 0, 0)
            self.MakeRadiusForIndices(obj, ndx1, ndx2)
            obj.location = (0,0,z)

        #*************************************************************************
        # Create Depth Image
        #*************************************************************************
        def CreateDepthImage(self):
            (z,SZ) = Blender4CNC.GetzSZ()
            verts = [(0,0,0), (SZ,0,0), (SZ,SZ,0), (0,SZ,0), (0,0,SZ)]
            edges = [[0,4], [4,1]]
            faces = [[0,1,2,3]]
            obj = self.CreatePocketPath(verts, edges, faces, "001.DepthImage.X")
            obj.location = (0,0,z)
            
            # Add a UV map or else the image texture will not appear
            m1 = obj.data
            m1.uv_layers.new(name="UVMap")
            
            mat = bpy.data.materials.new("Material")
            mat.use_nodes = True
            node_tree = mat.node_tree
            nodes = node_tree.nodes
            tex = nodes.new('ShaderNodeTexImage')
            tex.show_texture = True
            bsdf = nodes.get("Principled BSDF") 
            surf = bsdf.inputs[0]
            mat.node_tree.links.new(surf, tex.outputs[0])
            surf.show_expanded = True

            obj.data.materials.append(mat) # Set the material

        #*************************************************************************
        # Create Parameter
        #*************************************************************************
        def CreateParameter(self):
            # Get the active selected object
            obj = bpy.context.view_layer.objects.active
            obj = bpy.context.selected_objects
            if len(obj) == 0:
                raise Exception("Nothing selected!")
            obj = obj[0]
            
            (z,SZ) = Blender4CNC.GetzSZ()
            # Add a text object
            loc = obj.location
#            if (bpy.context.scene.unit_settings.system == "METRIC"):
#                bpy.ops.object.text_add(enter_editmode=False, align='WORLD', location=(loc.x, loc.y, loc.z+z), scale=(0.001, 0.001, 0.001))
#            else:
            bpy.ops.object.text_add(enter_editmode=False, align='WORLD', location=(loc.x, loc.y, loc.z+z), scale=(1, 1, 1))
            obj2 = bpy.context.view_layer.objects.active
            # Select just the text object, then the original object
            bpy.ops.object.select_all(action='DESELECT')
            obj2.select_set(state=True)
            obj.select_set(state=True)
            bpy.context.view_layer.objects.active = obj
            # Parent the parameter object to the operation
            bpy.ops.object.parent_set(type='OBJECT', keep_transform=False)
            # Set the text inside the parameter object
            obj2.data.body = "#Parameters"
            obj2.name = "Parameters"
            # Put the parameters object inside the same collection
            bpy.context.view_layer.active_layer_collection.collection.objects.unlink(obj2)
            obj.users_collection[0].objects.link(obj2)
            # Get material for Parameters if it exists
            if "Color4Parameters" in bpy.data.materials.keys():
                mat = bpy.data.materials["Color4Parameters"]
                obj2.data.materials.append(mat)
            # Set height of font
            if bpy.context.scene.unit_settings.system == "METRIC":
                obj2.data.size = 0.05
            else:
                obj2.data.size = 1 / Blender4CNC.METERS_TO_INCHES

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Class to handle the creation of things when in edit mode like curves, radii, etc.
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS EditOpsClass
    class EditOpsClass:

        def __init__(self, blender4CNCParent):
            self.parent = blender4CNCParent

        #*************************************************************************
        # Make Radius
        #*************************************************************************
        def MakeRadius(self):
            # Make sure we apply any scale etc.
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
            bpy.ops.object.editmode_toggle() # Back to edit mode

            # Get the selected vertices to see if there is an edge between them
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            if len(bpy.context.selected_objects) > 1:
                raise Exception("Multiple objects are selected.\nPlease select one object and then re-enter edit mode.")
            obj = bpy.context.selected_objects[0]
            verts = [vertex for vertex in obj.data.vertices if vertex.select]
            if len(verts) != 2:
                raise Exception("Please select exactly 2 points.")
            # Get the edge between the 2 points
            ndx1 = verts[0].index
            ndx2 = verts[1].index
            edges = [e for e in obj.data.edges if ndx1 in e.vertices]
            edges = [e for e in edges if ndx2 in e.vertices]
            bpy.ops.object.editmode_toggle() # Go back to edit mode

            # Add edge if there is none
            if len(edges) == 0:
                bpy.ops.mesh.edge_face_add()
                
            bpy.ops.mesh.mark_seam(clear=False)

        #*************************************************************************
        # Unmake Radius
        #*************************************************************************
        def UnmakeRadius(self):
            # Make sure we apply any scale etc.
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
            bpy.ops.object.editmode_toggle() # Back to edit mode

            bpy.ops.mesh.mark_seam(clear=True)

        #*************************************************************************
        # Set Origin to vertex
        #*************************************************************************
        def SetOriginToVertex(self):
            # Make sure we apply any scale etc.
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
            
            # Get the selected vertex
            verts = [vertex for vertex in bpy.context.selected_objects[0].data.vertices if vertex.select]
            if len(verts) != 1:
                raise Exception("Please select a single point.")
            loc = bpy.context.selected_objects[0].location # Get global location of object
            startVert = (verts[0].co.x + loc.x, verts[0].co.y + loc.y, verts[0].co.z + loc.z)
            bpy.ops.object.editmode_toggle() # Go back to edit mode
            saved_location = copy.copy(bpy.context.scene.cursor.location)
            
            bpy.ops.object.editmode_toggle() # Go to object mode 
            bpy.context.scene.cursor.location = Vector(startVert)
        
            bpy.ops.object.origin_set(type='ORIGIN_CURSOR')
            
            bpy.context.scene.cursor.location = saved_location
            bpy.ops.object.editmode_toggle() # Go back to edit mode

        #*************************************************************************
        # Create curve from 3 points
        #*************************************************************************
        def CreateCurveFrom3Points(self, context, clockwise):

            class M:
                pass

            m2 = context.scene.model2py3Point
            m = M()
            m.startX = m2.startX
            m.startY = m2.startY
            m.endX = m2.endX
            m.endY = m2.endY
            m.centerX = m2.centerX
            m.centerY = m2.centerY

            if bpy.context.scene.unit_settings.system == "IMPERIAL":
                m.startX *= Blender4CNC.INCHES_TO_METERS
                m.startY *= Blender4CNC.INCHES_TO_METERS
                m.endX *= Blender4CNC.INCHES_TO_METERS
                m.endY *= Blender4CNC.INCHES_TO_METERS
                m.centerX *= Blender4CNC.INCHES_TO_METERS
                m.centerY *= Blender4CNC.INCHES_TO_METERS

            # Toggle mode
            bpy.ops.object.mode_set(mode='OBJECT')  # return to object mode
            # Apply any scale
            bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
            bpy.ops.object.mode_set(mode='EDIT')

            v1 = (m.startX - m.centerX, m.startY - m.centerY)
            v2 = (m.endX - m.centerX, m.endY - m.centerY)

            x = v1[0]
            y = v1[1]
            m1 = sqrt(x**2 + y**2) # Length
            x = v2[0]
            y = v2[1]
            m2 = sqrt(x**2 + y**2) # Length

            if not Blender4CNC.FloatsAreEqual(m1, m2):
                raise Exception("Start and End points are not equal distance from Center point.")

            ang1 = Blender4CNC.Util2d.angle_signed(v1, (1,0,0))
            ang2 = Blender4CNC.Util2d.angle_signed(v2, (1,0,0))
            #print("ang1, ang2=", ang1, ang2)
            
            if ang1 < ang2:
                angDiff = math.pi * 2 - (ang2 - ang1)
            else:
                angDiff = ang1 - ang2
                
            angStep = angDiff / 4
            TenDegrees = (10 / 180) * math.pi
            if angStep > TenDegrees:
                n = int(angDiff / TenDegrees)
                angStep = angDiff / n


            mesh = bpy.context.object.data
            bm = bmesh.new()

            # convert the current mesh to a bmesh (must be in edit mode)
            bm.from_mesh(mesh)

            # Get the key points
            verts = [v for v in bm.verts if (Blender4CNC.FloatsAreEqual(m.startX, v.co.x) and Blender4CNC.FloatsAreEqual(m.startY, v.co.y) and Blender4CNC.FloatsAreEqual((v.co.z+1),1))]
            if len(verts) == 0:
                # Add the start point
                bm.verts.new((m.startX, m.startY, 0.0))
                verts = [v for v in bm.verts if (Blender4CNC.FloatsAreEqual(m.startX, v.co.x) and Blender4CNC.FloatsAreEqual(m.startY, v.co.y) and Blender4CNC.FloatsAreEqual((v.co.z+1),1))]
                #raise Exception("Cannot find start point in mesh.")
            if len(verts) > 1:
                raise Exception("Multiple vertices at start point in mesh.")
            startVert = verts[0]
            verts = [v for v in bm.verts if (Blender4CNC.FloatsAreEqual(m.endX, v.co.x) and Blender4CNC.FloatsAreEqual(m.endY, v.co.y) and Blender4CNC.FloatsAreEqual((v.co.z+1),1))]
            if len(verts) == 0:
                # Add the end point
                bm.verts.new((m.endX, m.endY, 0.0))
                verts = [v for v in bm.verts if (Blender4CNC.FloatsAreEqual(m.endX, v.co.x) and Blender4CNC.FloatsAreEqual(m.endY, v.co.y) and Blender4CNC.FloatsAreEqual((v.co.z+1),1))]
                #raise Exception("Cannot find end point in mesh.")
            if len(verts) > 1:
                raise Exception("Multiple vertices at end point in mesh.")
            endVert = verts[0]
            verts = [v for v in bm.verts if (Blender4CNC.FloatsAreEqual(m.centerX, v.co.x) and Blender4CNC.FloatsAreEqual(m.centerY, v.co.y) and Blender4CNC.FloatsAreEqual((v.co.z+1),1))]
            if len(verts) == 0:
                # Add the center point
                bm.verts.new((m.centerX, m.centerY, 0.0))
                verts = [v for v in bm.verts if (Blender4CNC.FloatsAreEqual(m.centerX, v.co.x) and Blender4CNC.FloatsAreEqual(m.centerY, v.co.y) and Blender4CNC.FloatsAreEqual((v.co.z+1),1))]
                #raise Exception("Cannot find center point in mesh.")
            if len(verts) > 1:
                raise Exception("Multiple vertices at center point in mesh.")
            centerVert = verts[0]

            x = v1[0]
            y = v1[1]
            m1 = sqrt(x**2 + y**2) # Length
            radius = m1
            z = 0
            count = 0
            listV = []
            
            #print("ang1, ang2=", ang1, ang2)
            #print("clockwise=", clockwise)
            if clockwise:
                if ang2 < ang1:
                    ang = ang1 - angStep
                    while (ang > ang2) and not Blender4CNC.FloatsAreEqual(ang, ang2):
                        count += 1
                        if count > 500:
                            # FAILS COVERAGE
                            break
                        x = m.centerX + math.cos(ang) * radius
                        y = m.centerY + math.sin(ang) * radius
                        vv = bm.verts.new((x,y,z))  # add a new vert
                        listV.append(vv)
                        ang -= angStep
                else:
                    # We are crossing the pi line
                    ang = ang1 - angStep
                    while (ang > -math.pi) and not Blender4CNC.FloatsAreEqual(ang, -math.pi):
                        #print("ang=", ang)
                        count += 1
                        if count > 500:
                            # FAILS COVERAGE
                            break
                        x = m.centerX + math.cos(ang) * radius
                        y = m.centerY + math.sin(ang) * radius
                        vv = bm.verts.new((x,y,z))  # add a new vert
                        listV.append(vv)
                        ang -= angStep
                    if Blender4CNC.FloatsAreEqual(ang, -math.pi):
                        ang = math.pi
                    # NO longer possible ?
                    #else:
                    #    ang += 2 * math.pi
                    while (ang > ang2) and not Blender4CNC.FloatsAreEqual(ang, ang2):
                        count += 1
                        if count > 500:
                            # FAILS COVERAGE
                            break
                        x = m.centerX + math.cos(ang) * radius
                        y = m.centerY + math.sin(ang) * radius
                        vv = bm.verts.new((x,y,z))  # add a new vert
                        listV.append(vv)
                        ang -= angStep
            else:
                if ang1 < ang2:
                    ang = ang1 + angStep
                    while (ang < ang2) and not Blender4CNC.FloatsAreEqual(ang, ang2):
                        count += 1
                        if count > 500:
                            # FAILS COVERAGE
                            break
                        x = m.centerX + math.cos(ang) * radius
                        y = m.centerY + math.sin(ang) * radius
                        vv = bm.verts.new((x,y,z))  # add a new vert
                        listV.append(vv)
                        ang += angStep
                else:
                    # We are crossing the pi line
                    ang = ang1 + angStep
                    while (ang < math.pi) and not Blender4CNC.FloatsAreEqual(ang, math.pi):
                        count += 1
                        if count > 500:
                            # FAILS COVERAGE
                            break
                        x = m.centerX + math.cos(ang) * radius
                        y = m.centerY + math.sin(ang) * radius
                        vv = bm.verts.new((x,y,z))  # add a new vert
                        listV.append(vv)
                        ang += angStep
                    if Blender4CNC.FloatsAreEqual(ang, math.pi):
                        ang = -math.pi
                    # No longer possible?
                    #else:
                    #    ang -= 2 * math.pi
                    while (ang < ang2) and not Blender4CNC.FloatsAreEqual(ang, ang2):
                        count += 1
                        if count > 500:
                            # FAILS COVERAGE
                            break
                        x = m.centerX + math.cos(ang) * radius
                        y = m.centerY + math.sin(ang) * radius
                        vv = bm.verts.new((x,y,z))  # add a new vert
                        listV.append(vv)
                        ang += angStep

            # Set the indices of vertices.
            bm.verts.index_update()
            bm.verts.ensure_lookup_table()
            point1 = (listV[0].co.x, listV[0].co.y)
            point2 = (listV[1].co.x, listV[1].co.y)
            pointLast = (listV[-1].co.x, listV[-1].co.y)
            
            # Create edges
            bm.edges.new((startVert, listV[0]))
            for i in range(0,len(listV)-1):
                bm.edges.new((listV[i], listV[i+1]))
            bm.edges.new((listV[-1], endVert))
            e = bm.edges.new((listV[1], centerVert))

            listV1_index = listV[1].index
            centerVert_index = centerVert.index

            ndx1 = startVert.index
            ndx2 = listV[0].index
            ndx3 = endVert.index
            ndx4 = listV[-1].index
                
            # make the bmesh the object's mesh
            bpy.ops.object.mode_set(mode='OBJECT')  # return to object mode
            bm.to_mesh(mesh)  
            bm.free()  # always do this when finished


            bpy.ops.object.mode_set(mode='EDIT')  # return to object mode
            bpy.ops.object.mode_set(mode='OBJECT')
            
            obj = bpy.context.object
            
            createOps = self.parent.CreateOps
            createOps.MakeCurveForIndices(obj, ndx1, ndx2)
            createOps.MakeCurveForIndices(obj, ndx3, ndx4)
            createOps.MakeRadiusForIndices(obj, listV1_index, centerVert_index)
            bpy.ops.object.mode_set(mode='EDIT')

            # Toggle mode
            bpy.ops.object.mode_set(mode='OBJECT')  # return to object mode
            bpy.ops.object.mode_set(mode='EDIT')

        #*************************************************************************
        # Create CW curve from 3 points
        #*************************************************************************
        def CreateShortCurve3Points(self, context):
            self.CreateCurveFrom3Points(context, True)
            return

        #*************************************************************************
        # Create CCW curve from 3 points
        #*************************************************************************
        def CreateCCWCurve3Points(self, context):
            self.CreateCurveFrom3Points(context, False)
            return

        #*************************************************************************
        # Make a segment a curve
        #*************************************************************************
        def MakeCurve(self):
            # Get the selected vertices to see if there is an edge between them
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            if len(bpy.context.selected_objects) > 1:
                raise Exception("Multiple objects are selected.\nPlease select one object and then re-enter edit mode.")
            obj = bpy.context.selected_objects[0]
            verts = [vertex for vertex in obj.data.vertices if vertex.select]
            if len(verts) != 2:
                raise Exception("Please select exactly 2 points.")
            # Get the edge between the 2 points
            ndx1 = verts[0].index
            ndx2 = verts[1].index
            edges = [e for e in obj.data.edges if ndx1 in e.vertices]
            edges = [e for e in edges if ndx2 in e.vertices]
            bpy.ops.object.editmode_toggle() # Go back to edit mode
            # Add edge if there is none
            if len(edges) == 0:
                bpy.ops.mesh.edge_face_add()
                
            bpy.ops.mesh.mark_freestyle_edge(clear=False)

        #*************************************************************************
        # Unmake a segment a curve
        #*************************************************************************
        def UnmakeCurve(self):
            bpy.ops.mesh.mark_freestyle_edge(clear=True)

        #*************************************************************************
        # Add a point
        #*************************************************************************
        def AddAPoint(self, context):
            m2p = context.scene.model2py
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                dist = m2p.distance
            else:
                dist = m2p.distance * 1 / Blender4CNC.METERS_TO_INCHES
            DEG2RAD = math.pi / 180
            x = math.cos(m2p.angle * DEG2RAD) * dist
            y = math.sin(m2p.angle * DEG2RAD) * dist
            bpy.ops.mesh.duplicate_move(MESH_OT_duplicate={"mode":1}, TRANSFORM_OT_translate={"value":(x, y, 0), "orient_type":'GLOBAL', "orient_matrix":((1, 0, 0), (0, 1, 0), (0, 0, 1)), "orient_matrix_type":'GLOBAL', "constraint_axis":(True, False, False), "mirror":False, "use_proportional_edit":False, "proportional_edit_falloff":'SMOOTH', "proportional_size":1, "use_proportional_connected":False, "use_proportional_projected":False, "snap":False, "snap_target":'CLOSEST', "snap_point":(0, 0, 0), "snap_align":False, "snap_normal":(0, 0, 0), "gpencil_strokes":False, "cursor_transform":False, "texture_space":False, "remove_on_cancel":False, "release_confirm":False, "use_accurate":False})

        #*************************************************************************
        # Make Start Point
        #*************************************************************************
        def MakeStartPoint(self, weight = 1):
            # Make sure we apply any scale etc.
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
            bpy.ops.object.editmode_toggle() # Back to edit mode

            # Get the selected vertex
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            verts = [vertex for vertex in bpy.context.selected_objects[0].data.vertices if vertex.select]
            if len(verts) != 1:
                raise Exception("Please select a single point.")
            startVert = (verts[0].co.x, verts[0].co.y, verts[0].co.z)
            bpy.ops.object.editmode_toggle() # Go back to edit mode
            # Duplicate vertex and move in Z
            (z,SZ) = Blender4CNC.GetzSZ()
            SZ = SZ/2
            bpy.ops.mesh.duplicate_move(MESH_OT_duplicate={"mode":1}, TRANSFORM_OT_translate={"value":(0, 0, SZ), "orient_type":'GLOBAL', "orient_matrix":((1, 0, 0), (0, 1, 0), (0, 0, 1)), "orient_matrix_type":'GLOBAL', "constraint_axis":(False, False, True), "mirror":False, "use_proportional_edit":False, "proportional_edit_falloff":'SMOOTH', "proportional_size":1, "use_proportional_connected":False, "use_proportional_projected":False, "snap":False, "snap_target":'CLOSEST', "snap_point":(0, 0, 0), "snap_align":False, "snap_normal":(0, 0, 0), "gpencil_strokes":False, "cursor_transform":False, "texture_space":False, "remove_on_cancel":False, "release_confirm":False, "use_accurate":False})
            # New vertex is selected, also select the original vertex
            bpy.ops.object.editmode_toggle() # Go to object mode
            # find the original start point and select it
            verts = [vertex for vertex in bpy.context.selected_objects[0].data.vertices]
            for i in range(0,len(verts)):
                vert = verts[i]
                if vert.co.x == startVert[0]:
                    if vert.co.y == startVert[1]:
                        if vert.co.z == startVert[2]:
                            vert.select = True
            bpy.ops.object.editmode_toggle() # Go back to edit mode
            bpy.ops.mesh.edge_face_add() # Add edge

            bpy.ops.object.editmode_toggle() # Go back to object mode
            # Find the indexes of the two selected vertices
            verts = [vertex for vertex in bpy.context.selected_objects[0].data.vertices]
            indexes = []
            for i in range(0,len(verts)):
                vert = verts[i]
                if vert.select:
                    indexes += [i]
            # Find the selected edge and set bevel_weight (start edge)
            if len(bpy.context.selected_objects) > 1:
                raise Exception("Multiple objects are selected.\nPlease select one object and then re-enter edit mode.")
            obj = bpy.context.selected_objects[0]
#            obj.data.use_customdata_edge_bevel = True
            edges = [e for e in obj.data.edges]
            edges2 = [e for e in edges if indexes[0] in e.vertices]
            edges2 = [e for e in edges2 if indexes[1] in e.vertices]
            edge = edges2[0]
            edge.bevel_weight = weight
            bpy.ops.object.editmode_toggle() # Go back to edit mode

        #*************************************************************************
        # Set coords for start of a curve
        #*************************************************************************
        def SetStartCurve(self, context):
            bpy.ops.object.mode_set(mode='OBJECT')  # return to object mode
            # Apply any scale
            bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
            bpy.ops.object.mode_set(mode='EDIT')
            v = self.CheckAndGetSingleSelectedVertex().co
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                context.scene.model2py3Point.startX = v.x
                context.scene.model2py3Point.startY = v.y
            else:
                context.scene.model2py3Point.startX = v.x * Blender4CNC.METERS_TO_INCHES
                context.scene.model2py3Point.startY = v.y * Blender4CNC.METERS_TO_INCHES

        #*************************************************************************
        # Set coords for end of a curve
        #*************************************************************************
        def SetEndCurve(self, context):
            # Make sure we apply any scale etc.
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
            bpy.ops.object.editmode_toggle() # Back to edit mode

            v = self.CheckAndGetSingleSelectedVertex().co
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                context.scene.model2py3Point.endX = v.x
                context.scene.model2py3Point.endY = v.y
            else:
                context.scene.model2py3Point.endX = v.x * Blender4CNC.METERS_TO_INCHES
                context.scene.model2py3Point.endY = v.y * Blender4CNC.METERS_TO_INCHES

        #*************************************************************************
        # 
        #*************************************************************************
        def CheckAndGetSingleSelectedVertex(self):
            # Get the selected vertex
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            verts = [vertex for vertex in bpy.context.selected_objects[0].data.vertices if vertex.select]
            if len(verts) != 1:
                raise Exception("Please select a single point.")
            bpy.ops.object.editmode_toggle() # Go back to edit mode
            return verts[0]

        #*************************************************************************
        # Set coords for center of a curve
        #*************************************************************************
        def SetCenterCurve(self, context):
            # Make sure we apply any scale etc.
            bpy.ops.object.editmode_toggle() # Go to object mode to update selected vertices
            bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)
            bpy.ops.object.editmode_toggle() # Back to edit mode

            v = self.CheckAndGetSingleSelectedVertex().co
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                context.scene.model2py3Point.centerX = v.x
                context.scene.model2py3Point.centerY = v.y
            else:
                context.scene.model2py3Point.centerX = v.x * Blender4CNC.METERS_TO_INCHES
                context.scene.model2py3Point.centerY = v.y * Blender4CNC.METERS_TO_INCHES

        #*************************************************************************
        # In edit mode, goes through all selected vertices and tries to find
        # curves (defined as a couple of curve segments that surround a radius 
        # and other points). Any complete curves that are found in the selected
        # vertices will be reduced to just their starting point
        #*************************************************************************
        def RemoveCurves(self, context) :
            try:

                bpy.ops.object.editmode_toggle() # Enter Object Mode
                b4c = self.parent
                b4c.Errors.DeleteWarningSpheres()
                b4c.Errors.DeleteErrorObjects()
                bpy.ops.object.editmode_toggle() # Enter Edit Mode

                if bpy.context.space_data.shading.type != 'WIREFRAME':
                    raise Exception("Please switch to wireframe and then select vertices.\n(Otherwise you may fail to select all the points\nthat you think you are selecting.)", (0,0))

                bpy.ops.object.editmode_toggle() # Enter Object Mode
                
                # First, find all radius edges in the selection
                if len(bpy.context.selected_objects) > 1:
                    raise Exception("Multiple objects are selected.\nPlease select one object and then re-enter edit mode.")
                obj = bpy.context.selected_objects[0]
                verts = obj.data.vertices 
                selectedVertices = [vertex.index for vertex in obj.data.vertices if vertex.select]
                edges = obj.data.edges
                selectedEdges = []
                for edge in edges:
                    if (edge.vertices[0] in selectedVertices) and (edge.vertices[1] in selectedVertices):
                        selectedEdges.append(edge)
                radiusEdges = []
                for edge in selectedEdges:
                    if edge.use_seam:
                        radiusEdges.append(edge)                    
                #print(selectedVertices)
                #print(edges)
                #print(selectedEdges)
                #print(radiusEdges)

                listOfDoubles = []
                
                for radEdge in radiusEdges:
                    # Find the vertex that branches off to other edges
                    v1 = radEdge.vertices[0]
                    v2 = radEdge.vertices[1]
                    v1Edges = [e for e in selectedEdges if e.vertices[0] == v1]
                    v1Edges += [e for e in selectedEdges if e.vertices[1] == v1]
                    v2Edges = [e for e in selectedEdges if e.vertices[0] == v2]
                    v2Edges += [e for e in selectedEdges if e.vertices[1] == v2]
                    if (len(v1Edges) == 1) and (len(v2Edges) == 3):
                        centerVertex = v1
                        radiusVertex = v2
                        followEdges = v2Edges
                    elif (len(v1Edges) == 3) and (len(v2Edges) == 1):
                        centerVertex = v2
                        radiusVertex = v1
                        followEdges = v1Edges
                    else:
                        # Bad match for a good curve, skip this radius edge
                        #print("BAD CURVE")
                        continue
                    #print("centerVertex, radiusVertex=", centerVertex, radiusVertex)
                    
                    # From the radius vertex, move left and right and follow until we hit 
                    # curve edges or run out of edges
                    # First, remove the radius edge
                    followEdges.remove(radEdge)
                    leftEdge = followEdges[0]
                    rightEdge = followEdges[1]
                    leftVertex = radiusVertex
                    rightVertex = radiusVertex
                    verticesToDelete = [radiusVertex]
                    jumpToNextRadiusEdge = False
                    
                    selectedEdges.remove(radEdge)
                    selectedEdges.remove(leftEdge)
                    selectedEdges.remove(rightEdge)
                    
                    count = 0
                    while True:
                        count += 1
                        if count > 1000:
                            # FAILS COVERAGE
                            raise Exception("Error in RemoveCurves - A curve has too many points?", (0,0))
                        
                        if leftEdge.vertices[0] == leftVertex:
                            nextVertex = leftEdge.vertices[1]
                        else:
                            nextVertex = leftEdge.vertices[0]
                        nextEdges = [e for e in selectedEdges if e.vertices[0] == nextVertex]
                        nextEdges += [e for e in selectedEdges if e.vertices[1] == nextVertex]
                        if leftEdge.use_freestyle_mark:
                            # We don't do this here in case there is a problem at the other end
#                            leftEdge.use_freestyle_mark = False
                            # This is a curve segment, we are done in this direction
                            verticesToDelete.append(nextVertex)
                            leftVertex = nextVertex
                            break
                        # If we do not have exactly 1 edges, then we have a multi-point
                        if len(nextEdges) != 1:
                            jumpToNextRadiusEdge = True
                            break
                        leftEdge = nextEdges[0]
                        selectedEdges.remove(leftEdge)
                        verticesToDelete.append(nextVertex)
                        leftVertex = nextVertex
                    #print("verticesToDelete=", verticesToDelete)
                    if jumpToNextRadiusEdge:
                        continue

                        
                    count = 0
                    while True:
                        #print("verticesToDelete=", verticesToDelete)
                        count += 1
                        if count > 1000:
                            # FAILS COVERAGE
                            raise Exception("Error in RemoveCurves - A curve has too many points?", (0,0))
                        
                        if rightEdge.vertices[0] == rightVertex:
                            # FAILS COVERAGE
                            nextVertex = rightEdge.vertices[1]
                        else:
                            nextVertex = rightEdge.vertices[0]
                        nextEdges = [e for e in selectedEdges if e.vertices[0] == nextVertex]
                        nextEdges += [e for e in selectedEdges if e.vertices[1] == nextVertex]
                        if rightEdge.use_freestyle_mark:
                            # Now we also remove the left edge
                            leftEdge.use_freestyle_mark = False
                            rightEdge.use_freestyle_mark = False
                            # This is a curve segment, we are done in this direction
                            verticesToDelete.append(nextVertex)
                            rightVertex = nextVertex
                            break
                        # If we do not have exactly 1 edges, then we have a multi-point
                        if len(nextEdges) != 1:
#                            XYZ
                            jumpToNextRadiusEdge = True
                            break
                        rightEdge = nextEdges[0]
                        selectedEdges.remove(rightEdge)
                        verticesToDelete.append(nextVertex)
                        rightVertex = nextVertex
                    #print("verticesToDelete=", verticesToDelete)
                    verticesToDelete.append(centerVertex)
                    #print("verticesToDelete=", verticesToDelete)
                    #print("leftVertex, rightVertex=", leftVertex, rightVertex)

                    if jumpToNextRadiusEdge:
                        continue

                    # Move all the vertices in this group to the same location at the left   
                    # but leave the rightmost point at it's location (we keep the start and end
                    # of the curve because other curves may be starting or ending at those points)            
                    co1x = obj.data.vertices[leftVertex].co.x
                    co1y = obj.data.vertices[leftVertex].co.y
                    co1z = obj.data.vertices[leftVertex].co.z

                    listOfDoubles += verticesToDelete
                    for ndx in verticesToDelete:
                        if ndx != rightVertex:
                            obj.data.vertices[ndx].co = Vector((co1x, co1y, co1z))

                    #self.EDIT_MODE_Deselect_All_OBJECT_MODE()

                    #bpy.ops.object.editmode_toggle() # Enter Edit Mode
                    #bpy.ops.mesh.merge(type='CENTER', uvs=False)
                    #bpy.ops.object.editmode_toggle() # Enter Object Mode
    
                # All curves to be removed should now have their vertices doubled up on each other
                # Remove duplicate vertices
                bpy.ops.object.editmode_toggle() # Enter Edit Mode
                bpy.ops.mesh.remove_doubles(threshold=Blender4CNC.ABS_TOLERANCE)
    #            bpy.ops.mesh.remove_doubles(threshold=0)
    #            bpy.ops.object.editmode_toggle() # Enter Object Mode
                
            except Exception as err:
                b4c.Errors.DisplayRedException(err)
                raise err
            return {"FINISHED"}

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Class to handle the display of errors
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS ErrorsClass
    class ErrorsClass:

        def __init__(self, blender4CNCParent):
            self.parent = blender4CNCParent

        def ShowErrorOnOperation(self, ob, errString):
            obErr = self.FindOrCreateErrorMessage("ErrorText-" + ob.name, [errString])
            obErr.location = Vector((ob.location.x, ob.location.y, ob.location.z + 0.01))

        #*************************************************************************
        # If the Red Error material already exists it will assign the material
        # to the mesh error object. If the red material does not exist, it will
        # create one and then assign it. 
        #*************************************************************************
        def SetErrorColorToRed(self, mesh):
            self.SetErrorColorToRedTrans2(mesh, "ErrorMat", "")
        def SetErrorColorToRedTrans(self, mesh):
            self.SetErrorColorToRedTrans2(mesh, "ErrorMatTrans", "BLEND")
        def SetErrorColorToRedTrans2(self, mesh, errMat, blendMethod):
            # See if the Error Material color already exists    
            errorMat = None    
            for mat in bpy.data.materials:
                if str(errMat) == mat.name:
                    errorMat = mat
                    break
            # Create the Error Material color if it was not found
            if errorMat == None:
                errorMat = bpy.data.materials.new(errMat)
                errorMat.diffuse_color = (1, 0, 0, 1)
#                errorMat.blend_method = "BLEND"
                if blendMethod != "":
                    errorMat.blend_method = blendMethod

            # Add the Error Material to the Error message  
            if "materials" in dir(mesh):   
                if len(mesh.materials) == 0:
                    mesh.materials.append(errorMat)
                else:
                    mesh.materials[0] = errorMat
            else:
                if len(mesh.data.materials) == 0:
                    mesh.data.materials.append(errorMat)
                else:
                    mesh.data.materials[0] = errorMat

        #*************************************************************************
        # Used to display an error message. If a text/font mesh already exists
        # we just re-use it, otherwise we create a new text object
        #*************************************************************************
        def FindOrCreateErrorMessage(self, errName, errArgs):

            # If left in edit mode can get context exceptions! (and crashes)
            # This crashes if there is no active object, or if the active object is not visible
            if bpy.context.view_layer.objects.active:
                # Make sure the "active" object is visible
                obj = bpy.context.view_layer.objects.active
                hidden = obj.hide_get()
                if hidden:
                    obj.hide_set(False)
                bpy.ops.object.mode_set(mode='OBJECT', toggle=False)
                if hidden:
                    obj.hide_set(True)

            # Find if an error text object already exists
#            self.parent.UnselectAllObjects()
            # Make sure NOTHING is selected in the scene/object
            bpy.ops.object.select_all(action='DESELECT')
            ob = None
            for obj in bpy.context.scene.objects:
                if obj.name == errName:
#                    self.parent.MakeThisObjectTheActiveObject(obj)
                    # Make object the active object in the scene
                    bpy.context.view_layer.objects.active = obj
                    ob = obj
                    ob.select_set(True)
            if ob == None:
                # Create an Error text object
                oldCollection = bpy.context.view_layer.active_layer_collection
                # Set active active collection to "Master Collection"
                bpy.context.view_layer.active_layer_collection = bpy.context.view_layer.layer_collection

                bpy.ops.object.text_add(location=(0,0,0.02), radius=0.5)
                ob=bpy.context.object
                ob.name = errName

                # Return to original collection
                bpy.context.view_layer.active_layer_collection = oldCollection
                
            # Don't worry - now I set the font size
            # Initially, the text in the text object will be "Text"
            # If we size the text to a height of 20mm (for example), then, for many fonts,
            # the size will get changed to 26mm (approximately) when we have letters like "g" which
            # "hang down below the line". So I set the text to "Tg" to get the end result a lot closer
            # to the desired size before we set the actual message.
            self.ScaleErrorMessage(ob)

            # Get a zOffset
            errorZOffset = self.parent.Parameters.ProjectParameter("MsgZOffset")
    #        par = self.GetMainParametersAsStrings("ProjectParameters")
    #        par = self.Get Parameters("ProjectParameters", par)
    #        
    #        if "MsgZOffset" in par:
    #            errorZOffset = float(par["MsgZOffset"])
    #        else:
    #            errorZOffset = 0.001

            if len(errArgs) > 1:
                (x,y) = errArgs[1]
            else:
                (x,y) = (0,0)

            # Place error message at location
            if (bpy.context.scene.unit_settings.system == "IMPERIAL"):
                x /= Blender4CNC.METERS_TO_INCHES
                y /= Blender4CNC.METERS_TO_INCHES
            ob.location = (x,y,errorZOffset)
                    
            ob.data.body = errArgs[0]
            self.SetErrorColorToRed(ob.data)
            return ob

        def ScaleErrorMessage(self, ob):
    #        errorZOffset = self.Parameters.Global("MsgHeight")
    #        try:
    #            x = self.projectParams
    #        except:
    #            par = self.GetMainParametersAsStrings("ProjectParameters")
    #            if par == None:
    #                raise Exception("Cannot find Project Parameters (needed for displaying error messages)?", (0,0))
    #            self.projectParams = self.Get Parameters("ProjectParameters", par)
    #            
    #        msgHeight = float(self.projectParams["MsgHeight"])
    #        msgHeight = float(self.Parameters.Global("MsgHeight"))
            ob.data.size = float(self.parent.Parameters.ProjectParameter("MsgHeight"))

        #*************************************************************************
        # Delete any previous error objects
        #
        # Operators are intended to be used by a user, trying to delete objects with operators
        # has problems with hidden objects, so just use the python api like "remove" with unlink
        #        self.UnselectAllObjects()
        #        for ob in bpy.data.objects:
        #            if ob.name == 'ErrorText':
        #                ob.hide_set(False)
        #                ob.select_set(True)
        #        bpy.ops.object.delete()
        #*************************************************************************
        def DeleteErrorObjects(self):
            l = copy.copy(bpy.data.objects.keys())
            l = [x for x in l if x[0:9] == "ErrorText"]
            for name in l:
                ob = bpy.data.objects[name]
                if ob:
                    bpy.data.objects.remove(ob, do_unlink=True)

        #*************************************************************************
        # Show a "Warning" donut around a vertex of an object
        #*************************************************************************
        def ShowWarningDonut(self, obj, ndx):
            v = obj.matrix_world @ obj.data.vertices[ndx].co
            bpy.ops.mesh.primitive_torus_add(align='WORLD', location=(v.x, v.y, v.z), rotation=(0.0, 0.0, 0.0), major_segments=24, minor_segments=6, mode='MAJOR_MINOR', major_radius=0.005, minor_radius=0.005/4, abso_major_rad=0.005+0.005/4, abso_minor_rad=0.005-0.005/4, generate_uvs=True)
            obj2 = bpy.context.view_layer.objects.active
            obj2.name = "WarningSphere"
            self.SetErrorColorToRedTrans(obj2.data)
            obj2.select_set(state=False)

        #*************************************************************************
        # De-select any "ErrorText" objects (if selected)
        #*************************************************************************
        def UnselectErrorText(self):
            # If any ErrorText is in the selected objects, unselect it
            for obj in bpy.context.selected_objects:
                if obj.name[0:9] == "ErrorText":
                    obj.select_set(state=False)

        #*************************************************************************
        # De-select any "WarningSphere" objects (if selected)
        #*************************************************************************
        def UnselectWarningSphere(self):
            # If any WarningSphere is in the selected objects, unselect it
            for obj in bpy.context.selected_objects:
                if obj.name[0:13] == "WarningSphere":
                    obj.select_set(state=False)

        #*************************************************************************
        # Delete all warning donuts
        #*************************************************************************
        def DeleteWarningSpheres(self):
            toRemove = []
            for obj in bpy.context.scene.objects:
                if obj.name[0:13] == "WarningSphere":
                    toRemove.append(obj.name)
            count = 0
            for name in toRemove:
                obj = bpy.data.objects[name]
                bpy.data.objects.remove(obj, do_unlink=True)
                count += 1
            return count

        #*************************************************************************
        def DisplayRedException(self, err):
            ob = self.FindOrCreateErrorMessage("ErrorText", err.args)

        #*************************************************************************
        # Show a "Warning" donut around a vertex of an object
        #*************************************************************************
        def ShowWarningDonutCoords(self, v):
            x = v.x
            y = v.y
            z = v.z
            if (bpy.context.scene.unit_settings.system == "IMPERIAL"):
                x /= Blender4CNC.METERS_TO_INCHES
                y /= Blender4CNC.METERS_TO_INCHES
                z /= Blender4CNC.METERS_TO_INCHES

            bpy.ops.mesh.primitive_torus_add(align='WORLD', location=(x, y, z), rotation=(0.0, 0.0, 0.0), major_segments=24, minor_segments=6, mode='MAJOR_MINOR', major_radius=0.005, minor_radius=0.005/4, abso_major_rad=0.005+0.005/4, abso_minor_rad=0.005-0.005/4, generate_uvs=True)
            obj2 = bpy.context.view_layer.objects.active
            obj2.name = "WarningSphere"
            self.parent.Errors.SetErrorColorToRedTrans(obj2.data)
            obj2.select_set(state=False)
            return (x,y,z)

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Class to handle mogrifying operations like expand, shrink, create path left/right
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS MogrifyOpsClass
    class MogrifyOpsClass:

        def __init__(self, blender4CNCParent):
            self.parent = blender4CNCParent

        #*************************************************************************
        # Create a path to the right of the current selected path
        #*************************************************************************
        def CreatePathLeft(self, context, dist, right) :
            try:
                # Get all selected objects
                if len(bpy.context.selected_objects) == 0:
                    raise Exception("Nothing selected!", (0,0))
                    
                if len(bpy.context.selected_objects) != 1:
                    raise Exception("Too many objects selected!", (0,0))

                if len(bpy.context.selected_objects) > 1:
                    raise Exception("Multiple objects are selected.\nPlease select one object and then try again.")
                ob = bpy.context.selected_objects[0]
                origObj = bpy.context.selected_objects[0]
                if not self.parent.IsObjectNamed(ob.name, "Path"):
                    raise Exception("Please select a path only!", (0,0))

                if (ob.users_collection == (bpy.data.scenes['Scene'].collection,)) or (len(ob.users_collection)==0):
                    raise Exception("Object must be in a collection!", (0,0))
                else:
#                    if len(ob.users_collection) > 0:
                    coll = ob.users_collection[0]
#                if len(ob.users_collection) > 0:
#                    coll = ob.users_collection[0]
#                else:
#                    raise Exception("Object must be in a collection!", (0,0))
                # Check that the object is in a collection (not the Master Collection)
                coll = ob.users_collection[0]


                (z,SZ) = Blender4CNC.GetzSZ()

                # Make sure we apply any scale etc.
                bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)

                self.parent.Errors.DeleteErrorObjects()
                self.parent.Errors.DeleteWarningSpheres()

                (isOK, vPoly) = self.parent.MeshCleanup.CheckSingleMesh(bpy.data.objects[ob.name], dist, temp4ExpandShrink=True)
                if not isOK:
                    raise Exception("Please fix potential warning points.\n(Points too close?)", (0,0))
                vPoly = self.parent.VisualPoly(ob.name, dist)
                vPoly.SetCoords()

                points = Blender4CNC.Polytoxogon([]).RightLeftFromPath(vPoly.coords2, dist, right)
                ob.select_set(state=False)

                if (bpy.context.scene.unit_settings.system != "METRIC"):
                    m = 1 / Blender4CNC.METERS_TO_INCHES
                    for i in range(0,len(points)):
                        if len(points[i]) == 2:
                            points[i] = (points[i][0] * m, points[i][1] * m)
                        else:
                            points[i] = (points[i][0] * m, points[i][1] * m, points[i][2] * m, points[i][3] * m, points[i][4])

                # Offset local points to origin
                p0 = points[0]
                for i in range(0,len(points)):
                    if len(points[i]) == 2:
                        #points[i] -= p0
                        x = points[i][0] - p0[0]
                        y = points[i][1] - p0[1]
                        points[i] = (x,y)
                    else:
                        x = points[i][0] - p0[0]
                        y = points[i][1] - p0[1]
                        z = points[i][2] - p0[0]
                        w = points[i][3] - p0[1]
                        CW = points[i][4]
                        points[i] = (x,y,z,w,CW)

                poly2 = Blender4CNC.Polytoxogon(points)
                poly2 = poly2.ApproximateCurves()
                points2 = poly2.points

                # Create a mesh
                if (bpy.context.scene.unit_settings.system == "METRIC"):
                    zStart = 0.01
                else:
                    zStart = 0.01 * 1 / Blender4CNC.METERS_TO_INCHES
                points3d = [(x[0], x[1], zStart) for x in points2]
                edges3d = [[ed, ed+1] for ed in range(0,len(points3d)-1)]
                # Add a point above start
                (z,SZ) = Blender4CNC.GetzSZ()
                points3d += [(points2[0][0], points2[0][1], SZ)]
                ndxUp = len(points3d)-1
                edges3d += [[0, len(points3d)-1]]
                edges3d += [[1, len(points3d)-1]]
                faces3d = [[0, 1, len(points3d)-1]]

                curvePoints = []
                # Add curve centers
                for pt in points:
                    if len(pt) > 2:
                        points3d += [(pt[2], pt[3], zStart)]
                        curvePoints += [(pt[2], pt[3], zStart)]

                # Find all curves, add radius edge and mark curves as "freestyle"
                curveNum = 0
                #print("points=", points)
                radiusList = []
                curveList = []
                for i in range(0, len(points)-1):
                    p1 = points[i]
                    p2 = points[i+1]
                    if len(p2) > 2:
                        # We have found a curve - find same points in approx. points list
                        for j in range(0, len(points2)):
                            pt = points2[j]
                            if (pt[0] == p1[0]) and (pt[1] == p1[1]):
                                ndx1 = j
                            if (pt[0] == p2[0]) and (pt[1] == p2[1]):
                                ndx2 = j
                        ndxC = len(points2) + curveNum + 1
                        curveNum += 1
                        #print(ndxC, ndx1)
                        edges3d += [[ndxC, ndx1+1]]
                        radiusList += [[ndxC, ndx1+1]]
                        curveList += [[ndx1, ndx1+1], [ndx2-1, ndx2]]

                mesh_data = bpy.data.meshes.new(ob.name + "_mesh")
                mesh_data.from_pydata(points3d, edges3d, faces3d)
                mesh_data.update()

                if right:
                    obj = bpy.data.objects.new(ob.name + "-Right", mesh_data)
                else:
                    obj = bpy.data.objects.new(ob.name + "-Left", mesh_data)
    #            obj = bpy.data.objects.new(ob.name + "-Right", mesh_data)
                obj.location = (p0[0], p0[1], ob.location[2])
                
    #            bpy.data.collections["Collection Out"].objects.link(obj)
                bpy.data.collections[coll.name].objects.link(obj)
                obj.select_set(state=True)

                # Mark the start point edge
#                obj.data.use_customdata_edge_bevel = True
                edges = [e for e in obj.data.edges]
                edges2 = [e for e in edges if 0 in e.vertices]
                edges2 = [e for e in edges2 if ndxUp in e.vertices]
                edge = edges2[0]
                edge.bevel_weight = 1

                # Mark the radii
                bpy.ops.object.editmode_toggle()
                bpy.ops.mesh.select_mode(type="VERT")
                bpy.ops.mesh.select_all(action = 'DESELECT')
                bpy.ops.object.editmode_toggle()
                for i in range(0,len(radiusList)):
                    ndx1 = radiusList[i][0]
                    ndx2 = radiusList[i][1]
                    obj.data.vertices[ndx1].select = True
                    obj.data.vertices[ndx2].select = True
                bpy.ops.object.editmode_toggle()
                bpy.ops.mesh.mark_seam(clear=False)
                bpy.ops.mesh.select_all(action = 'DESELECT')
                bpy.ops.object.editmode_toggle()

                # Mark the curves
                for i in range(0,len(curveList)):
                    ndx1 = curveList[i][0]
                    ndx2 = curveList[i][1]
                    bpy.ops.object.editmode_toggle()
                    bpy.ops.mesh.select_all(action = 'DESELECT')
                    bpy.ops.object.editmode_toggle()
                    obj.data.vertices[ndx1].select = True
                    obj.data.vertices[ndx2].select = True
                    bpy.ops.object.editmode_toggle()
                    bpy.ops.mesh.mark_freestyle_edge(clear=False)
                    bpy.ops.mesh.select_all(action = 'DESELECT')
                    bpy.ops.object.editmode_toggle()
                                                
            except Exception as err:
                ea = list(err.args)
                ob = self.parent.Errors.FindOrCreateErrorMessage("ErrorText", ea)
                raise err
            return {"FINISHED"}
        #end CreatePathLeft

        #*************************************************************************
        # Expand the current shape
        #*************************************************************************
        def ExpandShapeVPolyFromPoints(self, poly2, ob, points, points2, newName, coll):
            #print("ExpandShapeVPolyFromPoints")
            #print("points=", points)
            #print("points2=", points2)
            # Create a mesh
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                zStart = 0.01
            else:
                zStart = 0.01 * 1 / Blender4CNC.METERS_TO_INCHES
            # Just put the Z of the new shape at the same Z as the original object
            zStart = ob.data.vertices[0].co.z
            
            points3d = [(x[0], x[1], zStart) for x in points2]
            edges3d = [[ed, ed+1] for ed in range(0,len(points3d)-1)]
            edges3d += [[len(points3d)-1, 0]]
            # Add a point above start
            (z,SZ) = Blender4CNC.GetzSZ()
            points3d += [(points2[0][0], points2[0][1], SZ)]
            ndxUp = len(points3d)-1
            edges3d += [[0, len(points3d)-1]]
            edges3d += [[1, len(points3d)-1]]
            faces3d = [[0, 1, len(points3d)-1]]

            curvePoints = []
            # Add curve centers
            # If this is a closed path, then if the 1st point is a curve - it is really the last curve
            for i in range(1, len(points)):
                pt = points[i]
                if len(pt) > 2:
                    points3d += [(pt[2], pt[3], zStart)]
                    curvePoints += [(pt[2], pt[3], zStart)]
            pt = points[0]
            if len(pt) > 2:
                points3d += [(pt[2], pt[3], zStart)]
                curvePoints += [(pt[2], pt[3], zStart)]

            # Find all curves, add radius edge and mark curves as "freestyle"
            curveNum = 0
            #print("points=", points)
            radiusList = []
            curveList = []
            lastJ = 0
            for i in range(0, len(points)):
                p1 = points[i]
                if (i == (len(points)-1)):
                    p2 = points[0]
                else:
                    p2 = points[i+1]
                if len(p2) > 2:
                    #print("ExpandShapeVPolyFromPoints found curve")
                    # We have found a curve in the list of original points
                    # - find same points in points2 where we converted to an approximated curve
                    ndx1 = -1
                    ndx2 = -1
                    for j in range(lastJ, len(points2)):
                        pt = points2[j]
                        if (pt[0] == p1[0]) and (pt[1] == p1[1]):
                            ndx1 = j
                        if (pt[0] == p2[0]) and (pt[1] == p2[1]):
                            ndx2 = j
                        #print("ExpandShapeVPolyFromPoints ndx1, ndx2=", ndx1, ndx2)
                    specialCurve = False
                    if ndx2 == -1:
                        # Maybe we need to wrap back to the start
                        j = 0
                        pt = points2[j]
                        if (pt[0] == p2[0]) and (pt[1] == p2[1]):
                            ndx2 = j
                            specialCurve = True
                            
                    if ndx1 > lastJ:
                        lastJ = ndx1
                    if ndx2 > lastJ:
                        lastJ = ndx2
                    ndxC = len(points2) + curveNum + 1
                    curveNum += 1
                    #print(ndxC, ndx1)
                    edges3d += [[ndxC, ndx1+1]]
                    radiusList += [[ndxC, ndx1+1]]
                    if specialCurve:
                        curveList += [[ndx1, ndx1+1], [len(points2)-1, 0]]
                    else:
                        curveList += [[ndx1, ndx1+1], [ndx2-1, ndx2]]

            mesh_data = bpy.data.meshes.new(ob.name + "_mesh")
            mesh_data.from_pydata(points3d, edges3d, faces3d)
            mesh_data.update()

            obj = bpy.data.objects.new(newName, mesh_data)
            obj.location = (0, 0, ob.location.z)

    #            bpy.data.collections["Collection Out"].objects.link(obj)
            bpy.data.collections[coll.name].objects.link(obj)
            obj.select_set(state=True)

            # Mark the start point edge
            #obj.data.use_customdata_edge_bevel = True
            edges = [e for e in obj.data.edges]
            edges2 = [e for e in edges if 0 in e.vertices]
            edges2 = [e for e in edges2 if ndxUp in e.vertices]
            edge = edges2[0]
            edge.bevel_weight = 1

            # Mark the radii
            bpy.ops.object.editmode_toggle()
            bpy.ops.mesh.select_mode(type="VERT")
            bpy.ops.mesh.select_all(action = 'DESELECT')
            bpy.ops.object.editmode_toggle()
            for i in range(0,len(radiusList)):
                ndx1 = radiusList[i][0]
                ndx2 = radiusList[i][1]
                obj.data.vertices[ndx1].select = True
                obj.data.vertices[ndx2].select = True
            bpy.ops.object.editmode_toggle()
            bpy.ops.mesh.mark_seam(clear=False)
            bpy.ops.mesh.select_all(action = 'DESELECT')
            bpy.ops.object.editmode_toggle()

            # Mark the curves
            for i in range(0,len(curveList)):
                ndx1 = curveList[i][0]
                ndx2 = curveList[i][1]
                bpy.ops.object.editmode_toggle()
                bpy.ops.mesh.select_all(action = 'DESELECT')
                bpy.ops.object.editmode_toggle()
                obj.data.vertices[ndx1].select = True
                obj.data.vertices[ndx2].select = True
                bpy.ops.object.editmode_toggle()
                bpy.ops.mesh.mark_freestyle_edge(clear=False)
                bpy.ops.mesh.select_all(action = 'DESELECT')
                bpy.ops.object.editmode_toggle()

            #bpy.ops.object.origin_set(type='ORIGIN_CURSOR', center='MEDIAN')
            #obj.select_set(state=False)
            
            # Set the origin of the object to the first point
            self.parent.editOps = Blender4CNC.EditOpsClass(self.parent)
            # Select the first point
            bpy.ops.object.mode_set(mode = 'EDIT') 
            bpy.ops.mesh.select_mode(type="VERT")
            bpy.ops.mesh.select_all(action = 'DESELECT')
            bpy.ops.object.mode_set(mode = 'OBJECT')
            obj.data.vertices[0].select = True
            # Make sure this object is the only selected object
            bpy.ops.object.select_all(action='DESELECT') # Deselect all objects
            obj.select_set(state=True)
            bpy.context.view_layer.objects.active = obj
            # Go to edit mode and move the origin
            bpy.ops.object.mode_set(mode = 'EDIT') 
#            bpy.ops.object.mode_set(mode = 'OBJECT')
            # Now set the origin to it
#            bpy.ops.object.mode_set(mode = 'EDIT') 
            self.parent.editOps.SetOriginToVertex()
            bpy.ops.object.mode_set(mode = 'OBJECT')

            return obj

        def ExpandShape(self, context, dist, expand) :
            b4c = Blender4CNC()

            try:
                if (bpy.context.scene.unit_settings.system == "METRIC"):
                    dist *= 0.001

                # Get all selected objects
                if len(bpy.context.selected_objects) == 0:
                    raise Exception("Nothing selected!", (0,0))
                    
                if len(bpy.context.selected_objects) != 1:
                    raise Exception("Too many objects selected!", (0,0))

                ob = bpy.context.selected_objects[0]
                if len(bpy.context.selected_objects) > 1:
                    raise Exception("Multiple objects are selected.\nPlease select one object and then try again.")
                origObj = bpy.context.selected_objects[0]
                if not self.parent.IsObjectNamed(ob.name, "Path") and (not self.parent.IsObjectNamed(ob.name, "Pocket")) and (not self.parent.IsObjectNamed(ob.name, "Tenon")):
                    raise Exception("Please select a path or pocket only!", (0,0))


                if (ob.users_collection == (bpy.data.scenes['Scene'].collection,)) or (len(ob.users_collection)==0):
                    raise Exception("Object must be in a collection!", (0,0))
                else:
#                    if len(ob.users_collection) > 0:
                    coll = ob.users_collection[0]
#                    else:
#                        # FAILS COVERAGE
#                        raise Exception("Object must be in a collection!", (0,0))
                # Check that the object is in a collection (not the Master Collection)
                coll = ob.users_collection[0]

                (z,SZ) = Blender4CNC.GetzSZ()

                # Make sure we apply any scale etc.
                bpy.ops.object.transform_apply(location=False, rotation=True, scale=True)

                bpy.context.scene.cursor.location = ob.location

                # Check it is a closed shape
                self.parent.Errors.DeleteErrorObjects()
                self.parent.Errors.DeleteWarningSpheres()

                # A pocket/tenon is always "closed" when created
                (isOK, vPoly) = self.parent.MeshCleanup.CheckSingleMesh(bpy.data.objects[ob.name], dist, temp4ExpandShrink=True)
                if not isOK:
                    raise Exception("Please fix potential warning points.\n(Points too close?)", (0,0))
                
                # Check if the shape is closed
                # CheckSingleMesh returns a vPoly that has not necessarily verified that the vertices
                # form a closed shape - here we must look for an edge between the last and first vertices
                # THis is now done inside the VisualPoly class
#                p1 = vPoly.poly.lines[0][0]
#                p2 = vPoly.poly.lines[-1][1]
#                FEQ = Blender4CNC.FloatsAreEqual
#                closedShape = (FEQ(p1[0], p2[0]) and FEQ(p1[1], p2[1]))
#                l = [vPoly.indices[1][0], vPoly.indices[1][-1]]
#                print("ExpandShape l=", l)
#                obj2 = bpy.data.objects[vPoly.name]
#                edges = [e for e in obj2.data.edges]
#                print("ExpandShape edges=", edges)
#                e2 = [e for e in edges if e.vertices[0] in l]
#                print("ExpandShape e2=", e2)
#                e2 += [e for e in edges if e.vertices[1] in l]
#                print("ExpandShape e2=", e2)
#                e2 = [e for e in e2 if (e.vertices[0] in l) and (e.vertices[1] in l)]
#                print("ExpandShape e2=", e2)
#                closedShape = (len(e2) > 0)
#                # if closedShape is False, it may be because the "first" point is the end of a curve
#                if len(vPoly.indices[1][0]) > 2:
#                    print("ExpandShape", vPoly.closedShape)
#                    X

                # Reject open pockets/tenons
                if self.parent.IsObjectNamed(ob.name, "Pocket"):
                    if not vPoly.closedShape:
                        raise Exception("A Pocket shape must be closed!", p1)
                if self.parent.IsObjectNamed(ob.name, "Tenon"):
                    if not vPoly.closedShape:
                        raise Exception("A Tenon shape must be closed!", p1)

                FEQ = Blender4CNC.FloatsAreEqual
                if self.parent.IsObjectNamed(ob.name, "Path"):
                    # Check if the shape is closed
                    p1 = vPoly.coords2[0]
                    p2 = vPoly.coords2[-1]
                    closedShape = (FEQ(p1[0], p2[0]) and FEQ(p1[1], p2[1]))

                    # If trying to shrink an open path, there would be nothing
                    if (not closedShape) and (not expand):
                        raise Exception("Shape shrunk to nothing!", (0,0))

#                print("ExpandShape D vPoly.poly.lines=", vPoly.poly.lines)
                
                pocketIsCCW = False
                if self.parent.IsObjectNamed(ob.name, "Pocket") or self.parent.IsObjectNamed(ob.name, "Tenon"):
                    # Check the poly does not cross itself
    #                vPoly.poly.CrossesOverItself()  # Raise exception if crosses
                    vPoly.poly.IsValid()  # Raise exception if crosses
                    # Then check if CCW
                    if not vPoly.poly.PolyIsClockwise():
                        pocketIsCCW = True
                        vPoly.poly = vPoly.poly.ReverseLineDirections()
                    
                # If trying to expand an open path, we create a poly from path
                polyFromPath = False
                if self.parent.IsObjectNamed(ob.name, "Path") and (not closedShape):
                    temp = [x for x in vPoly.poly.points]
                    (poly, tenons) = Blender4CNC.Polytoxogon([]).PolyFromPath(temp, dist)
                    polyFromPath = True
                else:            
                    tenons = None
                    if expand:
                        poly = vPoly.poly.Expand(None, dist)
                        # We just take the 1st main poly - ignore any tenons (if any)
                        # Now we handle tenons!
#                        poly = poly[0]
                        (poly, tenons) = poly
                    else:
                        poly = vPoly.poly.Shrink(dist)
                        # We just take the 1st main poly
                        poly = poly[0]
                    if pocketIsCCW:
                        poly = poly.ReverseLineDirections()

                points = poly.points
                # No need to test this - the Shrink function will throw an exception if it shrinks to nothing
                #if len(points) == 0:
                #    raise Exception("Shape shrunk to nothing!", (0,0))

                ob.select_set(state=False)

                poly2 = poly.ApproximateCurves()
                points2 = poly2.points

                if (bpy.context.scene.unit_settings.system != "METRIC"):
                    m = 1 / Blender4CNC.METERS_TO_INCHES
                    for i in range(0,len(points2)):
                        if len(points2[i]) == 2:
                            points2[i] = (points2[i][0] * m, points2[i][1] * m)
                        # No need to handle "curve" points - they will never occur
                        #else:
                        #    points2[i] = (points2[i][0] * m, points2[i][1] * m, points2[i][2] * m, points2[i][3] * m, points2[i][4])
                    for i in range(0,len(points)):
                        if len(points[i]) == 2:
                            points[i] = (points[i][0] * m, points[i][1] * m)
                        else:
                            points[i] = (points[i][0] * m, points[i][1] * m, points[i][2] * m, points[i][3] * m, points[i][4])

                newName = ob.name
#                if polyFromPath: # If we expanded an open path into a pocket
#                    newName = newName.replace("Path", "Pocket")
                if expand:
                    newName = newName + "-Expand"
                else:
                    newName = newName + "-Shrink"
                parentObject = self.ExpandShapeVPolyFromPoints(poly2, ob, points, points2, newName, coll)
                #print("")

                #print("tenons=", tenons)
                if (tenons != None) and (len(tenons) > 0):
                    tenonChildren = []
                    for tenon in tenons:
                        #print("tenon.points=", tenon.points)
                        points = tenon.points
                        poly2 = tenon.ApproximateCurves()
                        points2 = poly2.points

                        if (bpy.context.scene.unit_settings.system != "METRIC"):
                            m = 1 / Blender4CNC.METERS_TO_INCHES
                            for i in range(0,len(points2)):
                                if len(points2[i]) == 2:
                                    points2[i] = (points2[i][0] * m, points2[i][1] * m)
                                # No need to handle "curve" points - they will never occur
                                else:
                                    # FAILS COVERAGE
                                    points2[i] = (points2[i][0] * m, points2[i][1] * m, points2[i][2] * m, points2[i][3] * m, points2[i][4])
                            for i in range(0,len(points)):
                                if len(points[i]) == 2:
                                    points[i] = (points[i][0] * m, points[i][1] * m)
                                else:
                                    points[i] = (points[i][0] * m, points[i][1] * m, points[i][2] * m, points[i][3] * m, points[i][4])

                        newName = ob.name
                        if polyFromPath: # If we expanded an open path into a pocket
                            newName = newName.replace("Path", "Tenon")
                        else:
                            newName = newName.replace("Pocket", "Tenon")
                        if expand:
                            newName = newName + "-Expand"
                        # It is not possible to produce tenons if shrinking a shape
                        #else:
                        #    newName = newName + "-Shrink"
                        tenonChild = self.ExpandShapeVPolyFromPoints(poly2, ob, points, points2, newName, coll)
                        tenonChild.location = (tenonChild.location.x, tenonChild.location.y, parentObject.location.z + 0.001)
                        tenonChildren.append(tenonChild)
                        
                    # Make tenons children of the pocket
                    for tenonChild in tenonChildren:
                        parentObject.select_set(state=True)
                        tenonChild.select_set(state=True)
                        # Make the parent object active
                        bpy.context.view_layer.objects.active = parentObject
                        bpy.ops.object.parent_set(type='OBJECT', keep_transform=False)
                        parentObject.select_set(state=False)
                        tenonChild.select_set(state=False)

            except Exception as err:
                ea = list(err.args)
                ob = self.parent.Errors.FindOrCreateErrorMessage("ErrorText", ea)
                raise err
            return {"FINISHED"}
        #end ExpandShape

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # Class to handle cleaning up meshes (checking and cleaning)
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS MeshCleanupClass
    class MeshCleanupClass:

        def __init__(self, blender4CNCParent):
            self.parent = blender4CNCParent

        #*************************************************************************
        # Select objects in list and activate one of them
        #*************************************************************************
        def SelectObjectsInList(self, context, originalList1, originalActiveObj):
            for oob in originalList1:
                oob.select_set(state=True)
            if originalActiveObj != None:
                context.view_layer.objects.active = originalActiveObj

        #*************************************************************************
        # Do all validation of operations/selected objects prior to running
        # CleanMeshes or CheckMeshes
        #*************************************************************************
        def PrepareToCheckMeshes(self, context):
            self.parent.Errors.UnselectErrorText()
            self.parent.Errors.UnselectWarningSphere()

            # Get all selected objects that are operations
            originalList1 = copy.copy(bpy.context.selected_objects)
            originalList = []
            for s in ["Pocket", "Path", "Hole", "Tenon"]:
                originalList += [ob for ob in originalList1 if self.parent.IsObjectNamed(ob.name, s)]

            if len(originalList) == 0:
                raise Exception("No valid operations selected!", (0,0))

            # Remember active object
            originalActiveObj = context.view_layer.objects.active
            if originalActiveObj not in originalList:
                originalActiveObj = None

            self.parent.Errors.DeleteWarningSpheres()
            self.parent.Errors.DeleteErrorObjects()

            # Deselect all objects
            for obj in originalList1:
                obj.select_set(state=False)

            return (originalList1, originalList, originalActiveObj)

        #*************************************************************************
        def CheckMeshes(self, context) :
            try:
                (originalList1, originalList, originalActiveObj) = self.PrepareToCheckMeshes(context)

                # Loop through all objects (that were selected) and merge close points that might 
                # cause math problems
                limit = 0.01 # (Inches)
                while len(originalList) > 0:
                    oob = originalList[0]
                    obj = originalList[0]
                    self.CheckSingleMesh(obj, 1, True)
                    originalList.pop(0)
                    
                # Loop through all objects (that were selected) and make them selected again!
                self.SelectObjectsInList(context, originalList1, originalActiveObj)
            except Exception as err:
                self.parent.Errors.DisplayRedException(err)
                raise err
            return {"FINISHED"}
        #end CheckMeshes

        #*************************************************************************
        def CheckSingleMesh(self, obj, dist, temp4ExpandShrink):
            #print("CheckSingleMesh")
            try:
                vPoly = self.parent.VisualPoly(obj.name, dist)
                vPoly.SetCoords(None, temp4ExpandShrink)
            except Exception as err:
                # Something about the path/pocket had such problems that we couldn't
                # create a VisualPoly from it 
                if len(err.args) >= 3: # If it has given us a specific vertex
                    curNdx = err.args[2]
                    self.parent.Errors.ShowWarningDonut(obj, curNdx)
                raise err                        
                
            closeArray = []
            l = []
                
            # Remember coords are in meters (from obj.data)!
            limit = 0.01 # (Inches)
            limit *= Blender4CNC.INCHES_TO_METERS

            # Go through all points and find ANY points that are within 0.01" of each other
            # But don't match with "up" vertices
            # We also don't need to concern ourselves with points that are internal to curves
            # because they play no part in math calculations (CSG etc.)
            # We also do not need to worry about radius center points
            
            # Find radius and internal curve points
            mainPoints = []
            radiusPoints = []
            internalPoints = []
            for pt in vPoly.indices[1]:
                if type(pt) == list:
                    mainPoints.append(pt[0])
                    radiusPoints.append(pt[1])
                    internalPoints += pt[2]
                else:
                    mainPoints.append(pt)
            
            for i in range(0, len(mainPoints)):
                for j in range(i+1, len(mainPoints)):
                    ndxi = mainPoints[i]
                    ndxj = mainPoints[j]
                    p1 = obj.data.vertices[ndxi].co
                    p2 = obj.data.vertices[ndxj].co
                    dx = p2[0] - p1[0]
                    dy = p2[1] - p1[1]
                    dz = p2[2] - p1[2]
                    d = math.sqrt(dx * dx + dy * dy)
                    exactlyEqual = Blender4CNC.FloatsAreEqual(p1[0], p2[0]) and Blender4CNC.FloatsAreEqual(p1[1], p2[1])
                    if (d < limit) and (dz < limit*5) and not exactlyEqual:
                        l.append(ndxi)
                        break
            
            # Create pointers at each problem vertex
            for i in l:
                self.parent.Errors.ShowWarningDonut(obj, i)
                
            if len(l) > 0:
                return (False, vPoly)
            else:
                return (True, vPoly)

        #*************************************************************************
        # For all selected objects, merge vertices that are so close they cause 
        # math limit errors (unnecessarily - probably can cut a shape without 
        # such resolution required).
        #
        # It cannot handle a problem with any point that has an "up" edge.
        #
        # There could also be non-consecutive points that are troublesome by being 
        # very close but it cannot automatically handle those either.
        #*************************************************************************
        def CleanMeshes(self, context) :
            try:
                (originalList1, originalList, originalActiveObj) = self.PrepareToCheckMeshes(context)

                # Loop through all objects (that were selected) and merge close points that might 
                # cause math problems
                limit = 0.01 # (Inches)
                faceVertices = []
                while len(originalList) > 0:
                    oob = originalList[0]
                    obj = originalList[0]
                    
                    try:
                        vPoly = self.parent.VisualPoly(obj.name, 1)
                        vPoly.SetCoords(None, True)
                    except Exception as err:
                        # Something about the path/pocket had such problems that we couldn't
                        # create a VisualPoly from it 
                        if len(err.args) >= 3: # If it has given us a specific vertex
                            curNdx = err.args[2]
                            self.parent.Errors.ShowWarningDonut(obj, curNdx)
                        raise err                        

                    # Is this a pocket which has a horizontal face?
                    pocketWithFace = False
                    pocketFaceZ = 0
                    if vPoly.IsNamed2("Pocket") or vPoly.IsNamed2("Tenon"):
                        for poly in oob.data.polygons:
                            zs = []
                            faceVertices = []
                            for i in range(0, len(poly.vertices)):
                                vx = poly.vertices[i]
                                zs.append(oob.data.vertices[vx].co.z)
                                faceVertices.append(poly.vertices[i])
                            if len(zs) > 0:
                                pocketFaceZ = zs[0]
                                pocketWithFace = True
                                for i in range(1,len(zs)):
                                    if zs[i] != pocketFaceZ:
                                        pocketWithFace = False
                                        break
                    #print(pocketWithFace, pocketFaceZ)

                    #print("Clean Meshes")
                    #print(vPoly.poly.points)
                    #print(vPoly.indices)
                    #print(vPoly.coords)

                    closeArray = []
                    indicesToDelete = []
                    edgesToCreate = []
                    edgeVectors = []

                    # Get a list of all vertices that are involved with "up" edges
                    upEdgeVertices = []
                    edges = obj.data.edges
                    edges2 = [e for e in edges if e.bevel_weight > 0]
                    upEdgeVertices = [e.vertices[0] for e in edges2]
                    upEdgeVertices += [e.vertices[1] for e in edges2]
                        
                    # Go through all points and find consecutive points that are within 0.01" of each other
                    for i in range(-1, len(vPoly.poly.points)-1):
                        p1 = vPoly.poly.points[i]
                        p2 = vPoly.poly.points[i+1]
                        dx = p2[0] - p1[0]
                        dy = p2[1] - p1[1]
                        d = math.sqrt(dx * dx + dy * dy)
                        exactlyEqual = Blender4CNC.FloatsAreEqual(p1[0], p2[0]) and Blender4CNC.FloatsAreEqual(p1[1], p2[1])
                        if (d < limit) and not exactlyEqual:
                            closeArray.append(True)
                        else:
                            closeArray.append(False)
                    
                    # Check if all points are close together!
                    # (Really tiny shape would shrink to a single point)
                    if not (False in closeArray):
                        raise Exception("Shape is so tiny it would disappear!\nWhy not just delete it?", (0,0))
                    
                    # Mark all points that are True (too close) to a prior "False" point
                    # as to be deleted. If we have a string of "True" points in a row,
                    # we will just delete the first one and then go process this operation 
                    # again after fixing it temporarily
                    #print("closeArray=", closeArray)
                    goAgain = False
                    for i in range(0, len(vPoly.indices[1])):
                        #print(vPoly.indices[1][i], closeArray[i])
                        if closeArray[i] == True:
                            next = (i + 1) % len(closeArray)
                            if (closeArray[i-1] == False):
                                l = vPoly.indices[1][i]
                                if type(l) == list:
                                    #print("eliminate curve endpoint")
                                    # We have a curve endpoint to eliminate
                                    indicesToDelete.append(l[0])
                                    indicesToDelete.append(l[1])
                                    indicesToDelete += l[2]
                                else:
                                    #print("eliminate straight endpoint")
                                    # We have a straight endpoint to eliminate
                                    indicesToDelete.append(l)
                                # We must create an edge between these points
                                edgesToCreate.append([vPoly.indices[1][i-1], vPoly.indices[1][next]])
                                # In the case of a curve, we need to be able to get the radius center point
                                edgeVectors.append([vPoly.indices[1][i-1], vPoly.indices[1][i]])
                                if (closeArray[next] == True):
                                    goAgain = True

                    #print("indicesToDelete=", indicesToDelete)
                    if not goAgain:
                        originalList.pop(0)

                    #print(indicesToDelete)
                    #print(edgesToCreate)
                    #print(edgeVectors)
                    #print(upEdgeVertices)
                    
                    # Check if any of the indices to be deleted are in the list of vertices
                    # which are involved with "up" edges
                    for ndx in indicesToDelete:
                        if ndx in upEdgeVertices:
                            # Just highlight this problem
                            self.parent.Errors.ShowWarningDonut(obj, ndx)
                            raise Exception("Could not complete cleaning mesh - need to manually fix\npoints with 'up' edges.", (0,0))
                    # Check if any of the "new" edges are in the list of vertices
                    # which are involved with "up" edges (this can be troublesome if
                    # a tiny curve is to be eliminated but contains the start flag - we can lose
                    # the start flag)
                    for ndx in edgesToCreate:
                        ndx1 = ndx[0]
                        ndx2 = ndx[1]
                        if ndx1 in upEdgeVertices:
                            # FAILS COVERAGE
                            # Just highlight this problem
                            self.parent.Errors.ShowWarningDonut(obj, ndx1)
                            raise Exception("Could not complete cleaning mesh - need to manually fix\npoints with 'up' edges.", (0,0))
                        if ndx2 in upEdgeVertices:
                            # Just highlight this problem
                            self.parent.Errors.ShowWarningDonut(obj, ndx2)
                            raise Exception("Could not complete cleaning mesh - need to manually fix\npoints with 'up' edges.", (0,0))
                        
                    # When working in Imperial, the coordinates of the vertices are *still* in metric
                    # (The VisualPoly class does a conversion for display to gcode)

                    #print("edgesToCreate=", edgesToCreate)
                    # Create "new" edges
                    for (pairI,pair) in enumerate(edgesToCreate):
                        firstPointIsCurve = (type(pair[0]) == list)
                        secondPointIsCurve = (type(pair[1]) == list)
                        
                        # Deselect all points
                        self.parent.EDIT_MODE_Deselect_All_OBJECT_MODE()
                        
                        # Select 1st point
                        if firstPointIsCurve:
                            obj.data.vertices[pair[0][0]].select = True
                        else:
                            obj.data.vertices[pair[0]].select = True
                        
                        # Select 2nd point
                        if secondPointIsCurve:
                            # This is a curve point vertex
                            obj.data.vertices[pair[1][2][0]].select = True
                        else:
                            obj.data.vertices[pair[1]].select = True
                            
                        bpy.ops.object.editmode_toggle() # Enter Edit Mode
                        bpy.ops.mesh.edge_face_add()     # Create edge between 2 points
                        if secondPointIsCurve:
                            # This is a curve vertex, also make this edge a curve
                            bpy.ops.mesh.mark_freestyle_edge(clear=False)
                        bpy.ops.object.editmode_toggle() # Enter Object Mode

                        # Deselect all points
                        self.parent.EDIT_MODE_Deselect_All_OBJECT_MODE()

                        if secondPointIsCurve:
                            # Select the center of the radius
                            # This is a curve vertex, also move the center of the arc
                            e1 = edgeVectors[pairI][0]
                            e2 = edgeVectors[pairI][1]
                            #print("e1, e2=", e1, e2)
                            if type(e1) == list:
                                e1 = e1[0]
                            if type(e2) == list:
                                e2 = e2[0]
                            #print("e1, e2=", e1, e2)
                            co1 = obj.data.vertices[e1].co
                            #print("Previous good point=", co1.x, co1.y)
                            co2 = obj.data.vertices[e2].co
                            #print("Point being deleted (moved to 1st)=", co2.x, co2.y)
    #                        print(co1.x, co1.y, co2.x, co2.y)
    #                        co1 = obj.matrix_world @ obj.data.vertices[e1].co
    #                        co2 = obj.matrix_world @ obj.data.vertices[e2].co
                            edgeV = (co1.x - co2.x, co1.y - co2.y)
                            edgeV = (edgeV[0]/2, edgeV[1]/2)
                            #print(co1.x, co1.y, co2.x, co2.y, edgeV)
                            #print("Point at center of curve=", obj.data.vertices[pair[1][1]].co.x, obj.data.vertices[pair[1][1]].co.y)

                            # Check equi-distance
                            p1 = co2
                            if type(pair[1]) == list:
                                ndx2 = pair[1][0]
                            else:
                                ndx2 = pair[1]
                            p2 = obj.data.vertices[ndx2].co
                            pCenter = obj.data.vertices[pair[1][1]].co
                            v1 = p1 - pCenter
                            v2 = p2 - pCenter
                            #if not Blender4CNC.FloatsAreEqual(v1.length, v2.length):
                            #    print("BEFORE MOVING NOT EQUAL", v1.length, v2.length, v1.x * v1.x + v1.y * v1.y, v2.x * v2.x + v2.y * v2.y)
                            #else:
                            #    print("BEFORE MOVING EQUAL", v1.length, v2.length)

                            v = obj.data.vertices[pair[1][1]].co
                            v = v + Vector((edgeV[0], edgeV[1], 0))
                            obj.data.vertices[pair[1][1]].co = v
                            if type(pair[0]) == list:
                                ndx1 = pair[0][0]
                            else:
                                ndx1 = pair[0]
                            if type(pair[1]) == list:
                                ndx2 = pair[1][0]
                            else:
                                ndx2 = pair[1]
                            #print("Point at end of curve=", obj.data.vertices[ndx2].co.x, obj.data.vertices[ndx2].co.y)
                            #print("Point at center of curve=", obj.data.vertices[pair[1][1]].co.x, obj.data.vertices[pair[1][1]].co.y)
                            #print("Moving center ", ndx1, ndx2, pair[1][1], obj.data.vertices[ndx1].co, obj.data.vertices[ndx2].co, v)
                            # Check equi-distance
                            p1 = obj.data.vertices[ndx1].co
                            p2 = obj.data.vertices[ndx2].co
                            pCenter = obj.data.vertices[pair[1][1]].co
                            v1 = p1 - pCenter
                            v2 = p2 - pCenter
                            if not Blender4CNC.FloatsAreEqual(v1.length, v2.length):
                                #print("NOT EQUAL", v1.length, v2.length, v1.x * v1.x + v1.y * v1.y, v2.x * v2.x + v2.y * v2.y)
                                # We have changed a curve and moved the center however, the math has
                                # worked such that the center is NOT equidistant from the curve points
                                # So we will pick a new center. Start by selecting a radius length
                                # that is the average of the two lengths
                                newLength = (v1.length + v2.length)/2
                                # Get the intersections of two circles centered on the curve end points
                                center1 = p1
                                center2 = p2
                                p1 = (center1.x - newLength, center1.y)
                                p2 = (center1.x + newLength, center1.y)
                                q1 = (center2.x - newLength, center2.y)
                                q2 = (center2.x + newLength, center2.y)
                                A = (p1, (p2[0], p2[1], center1[0], center1[1], 1))
                                B = (q1, (q2[0], q2[1], center2[0], center2[1], 1))
                                ints = Blender4CNC.Polytoxogon([]).GetIntersectionsBetweenTwoCircles(A, B)
                                #print("ints=", ints)
                                if len(ints) != 2:
                                    # This should never happen
                                    self.parent.Errors.ShowWarningDonut(obj, ndx1)
                                    raise Exception("Could not complete cleaning mesh - need to manually fix\npoints. Could not recreate curve properly.", (0,0))
                                # Find which intersection is closest to the original center
                                v1x = ints[0][0] - pCenter[0]                                
                                v1y = ints[0][1] - pCenter[1]  
                                v2x = ints[1][0] - pCenter[0]  
                                v2y = ints[1][1] - pCenter[1]  
                                len1Sqrd = v1x * v1x + v1y * v1y
                                len2Sqrd = v2x * v2x + v2y * v2y
                                if len1Sqrd <= len2Sqrd:
                                    newCenter = ints[0]
                                else:
                                    newCenter = ints[1]
                                #print("newCenter=", newCenter)
                                obj.data.vertices[pair[1][1]].co = Vector((newCenter[0], newCenter[1], obj.data.vertices[pair[1][1]].co.z))

                                # Now that we have tried to fix the equi-distance problem, let us
                                # verify it
                                # Check equi-distance
                                p1 = obj.data.vertices[ndx1].co
                                p2 = obj.data.vertices[ndx2].co
                                pCenter = obj.data.vertices[pair[1][1]].co
                                v1 = p1 - pCenter
                                v2 = p2 - pCenter
                                if not Blender4CNC.FloatsAreEqual(v1.length, v2.length):
                                    # Hopefully this never happens!
                                    self.parent.Errors.ShowWarningDonut(obj, ndx1)
                                    raise Exception("Could not complete cleaning mesh - need to manually fix\npoints. Could not recreate curve properly.", (0,0))
                    
                    #print("about to create face")
                    #print("indicesToDelete=", indicesToDelete)
                    #print("faceVertices=", faceVertices)
                    # Create a face if necessary
                    if pocketWithFace:
                        for ndx in indicesToDelete:
                            # An ndx *may* not be in the list if it was added as a radius center point
                            # - it is not part of the face
                            if ndx in faceVertices:
                                faceVertices.remove(ndx)
                        # Create a new face
                        # Deselect all points
                        self.parent.EDIT_MODE_Deselect_All_OBJECT_MODE()
                        
                        # Select face points
                        for ndx in faceVertices:
                            obj.data.vertices[ndx].select = True

                        bpy.ops.object.editmode_toggle() # Enter Edit Mode
                        bpy.ops.mesh.edge_face_add()     # Create face
                        bpy.ops.object.editmode_toggle() # Enter Object Mode

                        # De-select all vertices
                        self.parent.EDIT_MODE_Deselect_All_OBJECT_MODE()

                    # De-select all vertices
                    self.parent.EDIT_MODE_Deselect_All_OBJECT_MODE()

                    # Select all vertices to delete
                    for ndx in indicesToDelete:
                        obj.data.vertices[ndx].select = True
                        
                    bpy.ops.object.editmode_toggle() # Enter Edit Mode
                    bpy.ops.mesh.delete(type='VERT')
                    bpy.ops.object.editmode_toggle() # Enter Object Mode

                # Loop through all objects (that were selected) and make them selected again!
                self.SelectObjectsInList(context, originalList1, originalActiveObj)

                #print("Finished CleanMeshes")
            except Exception as err:
                self.parent.Errors.DisplayRedException(err)
                raise err
            return {"FINISHED"}
        #end CleanMeshes

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A Class to represent a polytoxogon on the Blender/GUI side of things
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS VisualPoly
    class VisualPoly:

        def __init__(self, oName, dia, coordList = None, temp4ExpandShrink=False):
            self.name = oName
            self.outName = "Out." + oName
            self.poly = None
            self.tenons = []
            self.dia = dia
            self.endDepth = -0.01

            # Set all debugging to False
            self.debug = {}
            method_list = [func for func in dir(self) if callable(getattr(self, func))]
            for fn in method_list:
                if fn[0] != '_':
                    methodName = self.__class__.__name__ + "." + fn
                    self.debug[methodName] = False
            
            self.approxPoly = None
            self.approxTenons = []
            self.closedShape = False
            
        def SetCoords(self, coordList = None, temp4ExpandShrink=False):
            #print("SetCoords")
            #print("SetCoords name=", self.name)
            #print("SetCoords coordList=", coordList)
            if coordList == None:
                self.indices = self.GetIndicesOfShapePoints()
                self.coords = self.GetCoordinatesForIndices()
                #print("SetCoords self.indices=", self.indices)
                #print("SetCoords self.coords=", self.coords)
                
                # Due to how Blender operates with units - if a GCode path is in IMPERIAL, we
                # must scale all the coordinates because Blender is essentially metric.
                if bpy.context.scene.unit_settings.system == "IMPERIAL":
                    self.coords = self.ConvertMeters2Inches(self.coords)

                self.coordsStr = self.Print2DCoordinatesForObject()
                self.coords2 = []
                for x in self.coords:
                    #print(format(x[0],'.20f'))
                    
                    # Because coordinates are stored at single precision (7-digits significant)
                    # We attempt to round to what the user probably intended before casting to a double
                    # we then hope that these values carry through calculations with sufficient precision!
                    prec = 5
                    x0 = round(x[0], prec)
                    x1 = round(x[1], prec)
                    if len(x) == 3:
                        self.coords2.append((x0,x1))
                    else:
                        x3 = round(x[3], prec)
                        x4 = round(x[4], prec)
                        x6 = round(x[6], prec)
                        self.coords2.append((x0,x1,x3,x4,x6))
            else:
                # Creating a hole directly from a coordinate
                self.indices = (0,[0])
                self.coords2 = coordList

            # Get center and radius for circle
            if self.IsCircle():
                self.cx = self.coords[1][3]
                self.cy = self.coords[1][4]
                dx = self.coords[1][0] - self.cx
                dy = self.coords[1][1] - self.cy
                self.r = math.sqrt(dx * dx + dy * dy)

            if temp4ExpandShrink:
                self.poly = Blender4CNC.Polytoxogon(self.coords2)
                self.tenons = []
            else:
                if self.IsNamed2("Pocket") and self.IsCircle():
                    self.poly = Blender4CNC.Polytoxogon(self.coords2)
                    self.tenons = []
                elif self.IsNamed2("Pocket"):
                    # A pocket must be a closed shape, so there must be an edge between the 
                    # last and first vertices
                    ob = bpy.data.objects[self.name]
                    edges = [e for e in ob.data.edges]
                    
                    self.poly = Blender4CNC.Polytoxogon(self.coords2)
                    # Watch out! Must handle shrinking of a counter-clockwise poly!
                    if not self.poly.PolyIsClockwise():
                        tempPoly = self.poly.ReverseLineDirections()
                        polyShrunk = tempPoly.Shrink(self.dia/2)
                        # We just use the 1st poly returned - later throw an exception
                        polyShrunk = polyShrunk[0]
                        polyShrunkExpand = polyShrunk.Expand(None, self.dia/2)
                        polyShrunk = polyShrunk.ReverseLineDirections()
                    else:                        
                        polyShrunk = self.poly.Shrink(self.dia/2)
                        # We just use the 1st poly returned - later throw an exception
                        polyShrunk = polyShrunk[0]
                        polyShrunkExpand = polyShrunk.Expand(None, self.dia/2)
                    self.poly = polyShrunkExpand
                    self.tenons = []
                elif self.IsNamed2("Path") and self.IsCircle():
                    temp = [x for x in self.coords2]
                    (poly, tenons) = Blender4CNC.Polytoxogon([]).PolyFromPath(temp, self.dia/2)
                    # The coordinates for a circle are a little weird for visualization - split into two semi-circles
                    self.poly = poly
                    if len(tenons) > 0:
                        self.tenons = tenons
                elif self.IsNamed2("Path") or self.IsNamed2("Hole"):
                    temp = [x for x in self.coords2]
#                    cProfile.runctx('(poly, tenons) = Blender4CNC.Polytoxogon([]).PolyFromPath(temp, self.dia/2)', globals(), locals())
                    (poly, tenons) = Blender4CNC.Polytoxogon([]).PolyFromPath(temp, self.dia/2)
                    self.poly = poly
                    self.tenons = tenons
                elif self.IsNamed2("DrillPath"):
                    temp = [x for x in self.coords2]
                    (poly, tenons) = Blender4CNC.Polytoxogon([]).PolyFromPath(temp, self.dia/2)
                    self.poly = poly
                    self.tenons = []
                elif self.IsNamed2("DepthImage"):
                    self.poly = Blender4CNC.Polytoxogon(self.coords2)
                    self.tenons = []
            # We just assume the poly is the first poly
            if type(self.poly) == list:
                self.poly = self.poly[0]
            return (self.poly, self.tenons)
            
        #********************************************************************
        # 
        #********************************************************************
        def ConvertMeters2Inches(self, l):
            m = Blender4CNC.METERS_TO_INCHES
            l2 = []
            for i in range(0,len(l)):
                p = l[i]
                x = p[0] * m
                y = p[1] * m
                z = p[2] * m
                if len(p) == 3:
                    p2 = (x,y,z)
                else:
                    p2 = (x,y,z, p[3]*m, p[4]*m, p[5]*m, p[6])
                l2.append(p2)
            return l2

        #********************************************************************
        # 
        #********************************************************************
        def DEBUG_METHOD_HEADER(self, tf=False):
            if not tf:
                return (0,0,0)
            methodName = self.__class__.__name__ + "." + inspect.stack()[1][3]
            indent = None
            indent = " " * len(inspect.stack()) * 2
            self.debug[methodName] = tf
            if self.debug[methodName]:
                print(indent, methodName, "*" * 30)
            return (methodName, indent, self.debug[methodName])

        #*************************************************************************
        # Return the object's BMesh
        # The object MUST be in EDIT mode
        #*************************************************************************
        def GetObjectBMesh(self, ob):
            bm = bmesh.from_edit_mesh(ob.data)
            bm.verts.ensure_lookup_table()
            return bm

        #*************************************************************************
        # Get the poly where all curves have been approximated by straight line
        # segments
        # This ASSUMES that this is for the purpose of visualizing in Blender
        # and therefore automatically converts to metric values if the units
        # are set to IMPERIAL
        #*************************************************************************
        def CalcApproxCurves(self):
            # Convert curves to line segments
            self.approxPoly = self.poly.ApproximateCurves()
            if len(self.tenons) > 0:
                tenons2 = []
                for tenon in self.tenons:
                    if type(tenon) == list:
                        tenon = tenon[0]
                    tenons2.append(tenon.ApproximateCurves())
                self.approxTenons = tenons2
            return (self.approxPoly, self.approxTenons)

        #*************************************************************************
        # Add tenons to a pocket
        #*************************************************************************
        def ScaleApproxPolyAndTenons(self, scale):
            self.approxPoly.ScalePolyPoints(scale) 
            for i in range(0,len(self.approxTenons)):
                self.approxTenons[i].ScalePolyPoints(scale) 
            return (self.approxPoly, self.approxTenons)
        
        #*************************************************************************
        # Add tenons to a pocket
        #*************************************************************************
        def AddTenonsToPocket(self, tenons):
            # Only do this for pockets
            if not self.IsNamed2("Pocket"):
                return

            self.tenons = []
            for tenon in tenons:
                vPoly2 = Blender4CNC.VisualPoly(tenon, self.dia)
                vPoly2.SetCoords()
                poly2 = Blender4CNC.Polytoxogon(vPoly2.coords2)
                self.tenons.append(poly2)

        #*************************************************************************
        # Given a list of coordinates returns a nice string of comma separated
        # values ready for printing
        #*************************************************************************
        def Print2DCoordinatesForObject(self):
            l = self.coords
            s = []
            for p in l:
                if len(p) == 3:
                    s += ["(%4.3f, %4.3f)" % (p[0], p[1])]
                else:
                    # We have a curve/arc
                    s += ["(%4.3f, %4.3f, %4.3f, %4.3f, %d)" % (p[0], p[1], p[3], p[4], p[6])]
            return ",".join(s)

        #*************************************************************************
        # Return True if the cross product is positive. The 2 vectors are formed
        # as (x,y) -> (xx, yy) and (x,y) -> (cx, cy)
        #*************************************************************************
        def CrossProductPositive(self, x,y,xx,yy,cx,cy):
            v1 = (xx - x, yy - y, 0)
            v2 = (cx - x, cy - y, 0)
            v3 = Blender4CNC.Util3d.cross3d(v1,v2)
            return v3[2] > 0
        
        #*************************************************************************
        # Switch to OBJECT mode
        #*************************************************************************
        def SwitchToObjectMode(self):
            if bpy.context.object.mode != "OBJECT":
                bpy.ops.object.mode_set(mode='OBJECT', toggle=False)
                    
        #*************************************************************************
        # Switch to EDIT mode
        #*************************************************************************
        def SwitchToEditMode(self):
            if bpy.context.object.mode != "EDIT":
                bpy.ops.object.mode_set(mode='EDIT', toggle=False)
     
        #*************************************************************************
        # Find an object by name
        #*************************************************************************
        def ReturnObjectByName (self, passedName= ""):
            return bpy.data.objects[passedName]

        #*************************************************************************
        # Return a list of points around a pocket/path
        # Returns actual 3d coordinates in global coordinates (by using the list
        # of indices)
        #*************************************************************************
        def GetCoordinatesForIndices(self) :
            oName = self.name
            l = self.indices[1]
            ob = self.ReturnObjectByName(oName)
            # Make object the active object in the scene
            bpy.context.view_layer.objects.active = ob
#            self.MakeThisObjectTheActiveObject(ob)

            self.SwitchToEditMode()
            bm = self.GetObjectBMesh(ob)
            coords = []
            for i in range(0,len(l)):
                ndx2 = l[i]
                if type(ndx2) == type(1):
                    v = ob.matrix_world @ bm.verts[ndx2].co
                    coords.append((v.x, v.y, v.z))
                else:
                    # We are dealing with an arc/curve
                    v = ob.matrix_world @ bm.verts[ndx2[0]].co # Matrix multiply for global coordinates
                    vCenter = ob.matrix_world @ bm.verts[ndx2[1]].co
                    # Determine clockwise or counter-clockwise
                    CW = 1
                    approxCurve = ndx2[2]
                    pCurve = approxCurve[1]
                    vCurve = ob.matrix_world @ bm.verts[pCurve].co # Matrix multiply for global coordinates
                    prevPoint = l[i-1]
                    if type(prevPoint) != type(1):
                        prevPoint = prevPoint[0]
                    vPrev = ob.matrix_world @ bm.verts[prevPoint].co # Matrix multiply for global coordinates
#                    cross = self.CrossProductPositive(vPrev.x,vPrev.y, vCenter[0], vCenter.y, vCurve[0], vCurve.y)
                    #print("GetCoordinatesForIndices bm.verts[prevPoint].co=", bm.verts[prevPoint].co)
                    #print("GetCoordinatesForIndices bm.verts[ndx2[0]].co=", bm.verts[ndx2[0]].co)
                    #print("GetCoordinatesForIndices bm.verts[pCurve].co=", bm.verts[pCurve].co)
                    #print("GetCoordinatesForIndices vCenter[0], vCenter[1], vPrev[0], vPrev[1], vCurve[0], vCurve[1]=", vCenter[0], vCenter[1], vPrev[0], vPrev[1], vCurve[0], vCurve[1])
                    cross = self.CrossProductPositive(vCenter[0], vCenter[1], vPrev[0], vPrev[1], vCurve[0], vCurve[1])
#                    if not cross:
                    if cross:
                        CW = -1
                    #print("GetCoordinatesForIndices CW=", CW)
                    coords.append((v.x, v.y, v.z, vCenter.x, vCenter.y, vCenter.z, CW))
                        
            self.SwitchToObjectMode()
            return coords
        
        #*************************************************************************
        # Used for debugging to print the edges from a list
        #*************************************************************************
        def PrintEdges(self, edges, indent = ""):
            print(indent, end="")
            for e in edges:
                print(" " + str(e.vertices[0]) + "-" + str(e.vertices[1]) + ",", end="")
            if len(edges) > 0:
                print(" ")
            pass # a line to trigger coverage counts properly

        #*************************************************************************
        # Given one index end of an edge, returns the other index end of the edge
        #*************************************************************************
        def GetEdgeOtherPoint(self, edge, ndx):
            if edge.vertices[0] == ndx:
                return edge.vertices[1]
            return edge.vertices[0]
            
        #*************************************************************************
        # Make object the active object in the scene
        #*************************************************************************
#        def MakeThisObjectTheActiveObject(self, ob):
#            bpy.context.view_layer.objects.active = ob

        #*************************************************************************
        # Return True if the name matches the string
        #*************************************************************************
        def IsObjectNamed(self, name, s):
            return (re.match("\d\d\d\." + s + "\.", name) != None)

        def IsNamed2(self, s):
            return (re.match("\d\d\d\." + s + "\.", self.name) != None)


        #*************************************************************************
        # Is this a circle
        #*************************************************************************
        def IsCircle(self):
            ind = self.indices[1]
            if (len(ind) == 2) and (type(ind[1]) == list):
                if ind[1][0] == ind[0]:
                    return True
            return False

        #*************************************************************************
        # Go around the Blender mesh object and determine the list of points
        # (their order and indices) that make the shape
        #*************************************************************************
        def GetIndicesOfShapePoints(self):
            oName = self.name
            ob = bpy.data.objects[oName]
            edges = [e for e in ob.data.edges]
#            self.MakeThisObjectTheActiveObject(ob)
            # Make object the active object in the scene
            bpy.context.view_layer.objects.active = ob
            verts = ob.data.vertices


            curNdx = -1
            nextNdx = -1
            edge = None
            startNdx = -1
            centerNdx = -1
            midNdx = -1
            startCurveNdx = -1
            curvePoints = []
            
            START = 1
            AT_MULTI_POINT = 2
            PRE_CURVE = 3
            CURVE = 4
            AT_POINT = 5
            ZERO_EDGES = 6
            DONE = 7

            # Check if we have an odd number of curve segments (indicating a missing curve segment)            
            curveSegments = [edge for edge in edges if edge.use_freestyle_mark]
            count = len(curveSegments)
            if (count/2) != int(count/2):
                raise Exception("Odd number of curve segments in " + self.name, (0,0))

            # Check if we have correct number of radius lines
            radiusSegments = [edge for edge in edges if edge.use_seam]
            countRadius = len(radiusSegments)
            if (count/2) != countRadius:
                raise Exception("Incorrect number of radius lines for the curve segments " + self.name, (0,0))
            
            
            
            ssm = START
            
            l = []
            while ssm != DONE:
                
                if ssm == START:
                    edges2 = [e for e in edges if e.bevel_weight == 1]
                    if len(edges2) == 0:
                        raise Exception("Cannot find start point for " + self.name, (0,0))
                    if len(edges2) > 1:
                        raise Exception("Found multiple start points for " + self.name, (0,0))
                    edge = edges2[0]
                        
                    if verts[edge.vertices[0]].co.z < verts[edge.vertices[1]].co.z:
                        curNdx = edge.vertices[0]
                    else:
                        # FAILS COVERAGE
                        curNdx = edge.vertices[1]
                    startNdx = curNdx
                    l.append(curNdx)
                    
                    # If the object is a hole, we just need to find the start point
                    if self.IsNamed2("Hole"):
                        ssm = DONE
                    else:
                        ssm = AT_MULTI_POINT
        
                elif ssm == AT_MULTI_POINT:
                    # Find the "up" edge
                    edges2 = [e for e in edges if (curNdx in e.vertices) and (e.bevel_weight > 0)]
                    
                    edges3 = edges2
                    if len(edges3) != 1:
                        raise Exception("Cannot find up edge at multi-point for " + self.name, (0,0), curNdx)
                    upEdge = edges3[0]
                    # Find the index of the "up" point
                    if verts[upEdge.vertices[0]].co.z > verts[upEdge.vertices[1]].co.z:
                        # FAILS COVERAGE
                        upNdx = upEdge.vertices[0]
                    else:
                        upNdx = upEdge.vertices[1]
                    # Get all the edges from the "up" point
                    edges2 = [e for e in edges if upNdx in e.vertices]
                    edges2.remove(upEdge)
                    if len(edges2) == 0:
                        # FAILS COVERAGE
                        raise Exception("Cannot find bevel edge at multi-point for " + self.name, (0,0), curNdx)
                    # Get the smallest bevel_weight edge
                    ndx = 0
                    smallest = edges2[0].bevel_weight
                    for i in range(1,len(edges2)):
                        if edges2[i].bevel_weight == smallest:
                            raise Exception("Cannot find next direction edge at multi-point for " + self.name, (0,0), curNdx)
                        if edges2[i].bevel_weight < smallest:
                            smallest = edges2[i].bevel_weight
                            ndx = i
                    bevelEdge = edges2[ndx]
                    nextNdx = self.GetEdgeOtherPoint(bevelEdge, upNdx)
                    edges.remove(bevelEdge)
                    # Get all the edges from the "up" point again
                    edges2 = [e for e in edges if upNdx in e.vertices]
                    # If we have used all bevel edges from this point, remove the "up" edge
                    if len(edges2) == 1:
                        edges.remove(edges2[0])
                    # Get the edge from curNdx to nextNdx
                    edges2 = [e for e in edges if curNdx in e.vertices]
                    edges2 = [e for e in edges2 if nextNdx in e.vertices]
                    if len(edges2) != 1:
                        raise Exception("Cannot find next direction edge at multi-point for " + self.name, (0,0), curNdx)
                    # Check if this is the start of a curve
                    edge = edges2[0]
                    if edge.use_freestyle_mark:
                        ssm = PRE_CURVE
                    else:
                        # A straight segment, add in the point
                        curNdx = nextNdx
                        l.append(curNdx)
                        edges.remove(edge)
                        ssm = AT_POINT
                # END elif ssm == AT_MULTI_POINT:

                elif ssm == PRE_CURVE:

                    # Check if there is a radius line edge attached and give warning/error
                    edges2 = [e for e in edges if curNdx in e.vertices]
                    # Are any of the edges a radius?
                    edges3 = [e for e in edges2 if e.use_seam == True]
                    if len(edges3) != 0:
                        # FAILS COVERAGE
                        raise Exception("Cannot attach a radius line to the start of a curve for " + self.name, (0,0), curNdx)

                    startCurveNdx = curNdx
                    curNdx = self.GetEdgeOtherPoint(edge, curNdx)
                    curvePoints = [curNdx]
                    # Remove the edge we just traversed 
                    edges.remove(edge)
                    # We have not found the center of this curve yet
                    centerNdx = -1
                    ssm = CURVE
                # END elif ssm == PRE_CURVE:

                elif ssm == CURVE:
                    # Get the next edge (should only be one along a curve unless there is a radius)
                    edges2 = [e for e in edges if curNdx in e.vertices]
                    # Are any of the edges a radius?
                    edges3 = [e for e in edges2 if e.use_seam == True]
                    if len(edges3) != 0:
                        # We have discovered a radius
                        centerNdx = self.GetEdgeOtherPoint(edges3[0], curNdx)
                        midNdx = curNdx
                        edges.remove(edges3[0])
                        continue # Back to top of while loop
                    # Get the next edge (should only be one)
                    edges2 = [e for e in edges if curNdx in e.vertices]
                    if len(edges2) != 1:
                        raise Exception("Too many edges from curve point for " + self.name, (0,0), curNdx)
                    edge = edges2[0]
                    # Check if we have hit the end of the curve yet
                    if not edge.use_freestyle_mark:
                        # Not yet
                        curNdx = self.GetEdgeOtherPoint(edge, curNdx)
                        curvePoints.append(curNdx)
                        edges.remove(edge)
                        continue # Back to top of while loop
                        
                    # If we reach here, we are ending the curve
                    if centerNdx == -1:
                        raise Exception("Cannot find center of curve for " + self.name, (0,0), curNdx)
                    curNdx = self.GetEdgeOtherPoint(edge, curNdx)

                    # Check that the curve is valid (end points are same distance from center)
                    p1 = verts[startCurveNdx].co
                    p2 = verts[curNdx].co
                    pCenter = verts[centerNdx].co
                    v1 = p1 - pCenter
                    v2 = p2 - pCenter
                    if not Blender4CNC.FloatsAreEqual(v1.length, v2.length):
                        s2 = "startCurveNdx=" + str(startCurveNdx) + ", curNdx=" + str(curNdx) + ", centerNdx=" + str(centerNdx)
                        s2 += "\n p1=" + str(p1) + ", p2=" + str(p2)
                        s2 += "\n center=" + str(pCenter)
                        s2 += "\n v1=" + str(v1) + ", v2=" + str(v2)
                        s2 += "\n length1=" + str(v1.length) + ", length2=" + str(v2.length)
                        s2 += "\n diff=" + str(v1.length-v2.length)
                        s2 += "\n Invalid curve - end points not equidistant from center for " + self.name
                        raise Exception(s2, (ob.location.x,ob.location.y), curNdx)

                    l.append([curNdx, centerNdx, curvePoints])
                    edges.remove(edge)
                    ssm = AT_POINT
                # END elif ssm == CURVE:

                elif ssm == AT_POINT:
                    # Get all edges from this point
                    edges2 = [e for e in edges if curNdx in e.vertices]
                        
                    # Check if we have run into a radius without being in a curve!
                    edgesRadius = [e for e in edges2 if e.use_seam == True]
                    if len(edgesRadius) > 0:
                        raise Exception("Found a radius that is not inside a curve " + self.name + "\n(Note: the Start Flag should NOT be placed inside a curve.)", (0,0), curNdx)
                    
                    # If this point happens to also be used as the center of a curve - ignore the radius edge connected to it
                    edges2 = [e for e in edges2 if e.use_seam == False]
                    if len(edges2) == 0:
                        ssm = ZERO_EDGES
                        continue # Back to top of while loop
                    if len(edges2) > 1:
                        ssm = AT_MULTI_POINT
                        continue # Back to top of while loop
                    edge = edges2[0]
                    if edge.use_freestyle_mark:
                        ssm = PRE_CURVE
                        continue # Back to top of while loop
                    curNdx = self.GetEdgeOtherPoint(edge, curNdx)
                    edges.remove(edge)
                    l.append(curNdx)
                # END elif ssm == AT_POINT:
                    
                elif ssm == ZERO_EDGES:
                    if curNdx != startNdx:
                        # Must be open mesh
                        # This is NOT a closed shape
                        self.closedShape = False
                        ssm = DONE
                    else:
                        self.closedShape = True
                        # Was the last thing we did the end of a curve?
                        last = l[-1]
                        # Only want to do this for pockets not paths
                        if self.IsNamed2("Pocket") or self.IsNamed2("Tenon") or self.IsNamed2("DepthImage"):
                            if type(last) == list:
                                # Only do this if this is NOT a circle!
                                if (len(l) == 2) and (l[0] == last[0]):
                                    pass
                                else:
                                    # Move the "last entry" to over the "first"
                                    l[0] = l[-1]
                                    # Get rid of the "last" entry
                                    l.pop(-1)
                            else:
                                # A straight end
                                if last == l[0]:
                                    l.pop(-1)
                    ssm = DONE                        
                # END elif ssm == ZERO_EDGES:

                
            # End ssm while
            return (True, l)

        #*************************************************************************
        # Joins any tenons that overlap 
        #*************************************************************************
        def JoinOverlappingVisualTenons(self):
            # Only do this for pockets
            if not self.IsNamed2("Pocket"):
                return

            dist = self.dia/2
            # Expand all the tenons in the list
            tenons2 = []
            for tenon in self.tenons:
                if type(tenon) == list:
                    tenons2.append(tenon[0])
                else:
                    tenons2.append(tenon)
            self.tenons = tenons2
            if type(self.poly) == list:
                self.poly = self.poly[0]
            tenons = self.poly.ExpandPolys(self.tenons, dist)
            # If any tenon shapes, when expanded, produce "inner tenons" we ignore them
            tenons = [x[0] for x in tenons]
            joinedTenonsList = self.poly.JoinOverlappingPolys(tenons)
            joinedTenonsList2 = self.poly.ShrinkPolys(joinedTenonsList, dist)

    #        # There can be a case where a tenon forms a ring and there is a smaller
    #        # tenon iside the ring - it can pass the tests of being not overlapped and not inside
    #        # and we must do a special test
    #        i = 0
    #        countI = 0
    #        while i < len(joinedTenonsList2):
    #            countI += 1
    #            if countI > len(joinedTenonsList2):
    #                raise Exception("JoinOverlappingVisualTenons stuck in infinite i loop?", (0,0))
    #            j = i + 1
    #            iPopped = False
    #            countJ = 0
    #            while j < len(joinedTenonsList2):
    #                countJ += 1
    #                if countJ > len(joinedTenonsList2):
    #                    raise Exception("JoinOverlappingVisualTenons stuck in infinite j loop?", (0,0))
    #                if j == i:
    #                    continue
    #                tenonI = joinedTenonsList2[i]
    #                tenonJ = joinedTenonsList2[j]
    #                if tenonI.WillBeCompletelyInside(tenonJ, self.dia/2):
    #                    joinedTenonsList2.pop(j)
    #                    break
    #                elif tenonJ.WillBeCompletelyInside(tenonI, self.dia/2):
    #                    joinedTenonsList2.pop(i)
    #                    iPopped = True
    #                    break
    #                j += 1
    #                if j > 5:
    #                    break
    #            if not iPopped:
    #                i += 1
    #            if i > 5:
    #                break
    #        print("joinedTenonsList2=", joinedTenonsList2)
    #        if len(joinedTenonsList2) > 0:
    #            print("joinedTenonsList2[0]=", joinedTenonsList2[0].points)
            self.tenons = joinedTenonsList2

        #*************************************************************************
        # Joins any tenons that overlap the main poly to the main poly
        #*************************************************************************
        def JoinOverlappingVisualTenonsToPoly(self):
            # Only do this for pockets
            if not self.IsNamed2("Pocket"):
                return
            if self.tenons == []:
                return
            
            dist = self.dia/2
            # Expand all the tenons, shrink the poly
            if (len(self.tenons) > 0) and (type(self.tenons[0]) == list):
                tempList = [x[0] for x in self.tenons]
                tenons = self.poly.ExpandPolys(tempList, dist)
            else:
                tenons = self.poly.ExpandPolys(self.tenons, dist)
            # If any tenon shapes, when expanded, produce "inner tenons" we ignore them
            tenons = [x[0] for x in tenons]
            mainPoly = self.poly.Shrink(dist)
            mainPoly = mainPoly[0]
            # After expanding, the tenons may overlap with the edge of the pocket
            (mainPoly, tenons) = mainPoly.SubtractEdgeTenonsFromPoly(mainPoly, tenons)
            mainPoly = mainPoly[0]
            # Expand the poly and shrink the tenons
            self.poly = mainPoly.Expand(None, dist)
            # final expanded tenons will have to be shrunk back
            self.tenons = mainPoly.ShrinkPolys(tenons, dist)

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A class to process the collections of operations and paths
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #COVERAGE_CLASS ProcessCollections
    class ProcessCollections:
    
        def __init__(self, par):
            self.parent = par

        #*************************************************************************
        #
        #*************************************************************************
        def ProcessCollections(self, context):
            # Get the GUI parameters
            m2p = context.scene.model2py
            self.m2p = context.scene.model2py
            
            print("*********************************************")
            print("Blender4CNC")
            print("*********************************************")

            self.parent.Errors.DeleteErrorObjects()
            self.parent.Errors.DeleteWarningSpheres()
            self.DeleteCalculatedObjects()

            # Check we have a Version Object
            self.parent.Parameters.SetProjectParameters()
            self.parent.Parameters.CheckProjectParameters()
                
            # Check we have GCode Pre and Post Amble
            gcodePreAmble = self.parent.GetTextObject("GCodePreAmble")
            if gcodePreAmble == None:
                raise Exception("Cannot find GCode PreAmble Text?", (0,0))
            gcodePostAmble = self.parent.GetTextObject("GCodePostAmble")
            if gcodePostAmble == None:
                raise Exception("Cannot find GCode PostAmble Text?", (0,0))

            # Get global default parameters
            self.parent.Parameters.SetGlobalJobParameters()

            # Check if there are any object that are linked to an operation but are not in the same collection
            for obj in bpy.data.objects:
    #            if obj.name[0:10] == "Parameters":
                if True:
                    if obj.parent != None:
                        coll1 = obj.parent.users_collection
                        if len(coll1) == 0:
                            coll1 = None
                            raise Exception(obj.name + " is not in a collection.", (0,0))
                        else:
                            coll1 = coll1[0]
                        coll2 = obj.users_collection
                        if len(coll2) == 0:
                            coll2 = None
                        else:
                            coll2 = coll2[0]
                        if coll1 != coll2:
                            if coll2 != None:
                                coll2.objects.unlink(obj)
                            coll1.objects.link(obj)
                            
            errorZOffset = self.parent.Parameters.ProjectParameter("MsgZOffset")

            # Check if any operations are in the main collections
            for ob in bpy.data.objects:
                if (self.parent.IsObjectNamed(ob.name, "DepthImage") or self.parent.IsObjectNamed(ob.name, "Pocket") or self.parent.IsObjectNamed(ob.name, "Path") or self.parent.IsObjectNamed(ob.name, "Hole") or self.parent.IsObjectNamed(ob.name, "DrillPath") or self.parent.IsObjectNamed(ob.name, "Tenon")):
                    if len(ob.users_collection) > 0:
                        coll = ob.users_collection[0]
                    else:
                        # FAILS COVERAGE
                        coll = None
                        bpy.data.objects.remove(ob, do_unlink=True)
                        continue
                    
                    # Check if in main collection or the 2 special ones
                    if (coll == bpy.data.scenes['Scene'].collection): 
                        self.parent.Errors.ShowErrorOnOperation(ob, "Cannot have %s in the Scene Collection." % ob.name)
                    if (coll.name == "Collection 0 Globals"): 
                        self.parent.Errors.ShowErrorOnOperation(ob, "Cannot have %s in Collection 0 Globals." % ob.name)
                    if (coll.name == "Collection Out"): 
                        self.parent.Errors.ShowErrorOnOperation(ob, "Cannot have %s in Collection Out" % ob.name)


            self.ss = self.GetProgramHeader(gcodePreAmble)

            self.progNumber = 1

            self.listPrograms = []
            self.listProgramsCutter = []

            # Check these are visible
            if not self.IsCollectionVisible("Collection 0 Globals"):
                self.MakeCollectionVisible("Collection 0 Globals")
            if not self.IsCollectionVisible("Collection Out"):
                self.MakeCollectionVisible("Collection Out")
                
            if not self.IsCollectionVisible("Collection 0 Globals"):
                # FAILS COVERAGE
                raise Exception("Collection 0 Globals is not visible - do you need to click the eye icon in the outliner window?", (0,0))
            # Create a collection to hold the path models
            self.CreateCollectionOut()

            # Process all collections, operations to create the python programs
            listOfLists = self.GetGCode4Collections(gcodePreAmble, gcodePostAmble)
            #print("listOfLists=", listOfLists)

            if (len(listOfLists) == 0) or (len(listOfLists[0]) == 0):
                raise Exception("Nothing to program? Are the paths/collections visible and correctly named?", (0,0))

            return listOfLists


        #*************************************************************************
        # Delete any previous calculated objects (such as the piece of material
        # or paths)
        #*************************************************************************
        def DeleteCalculatedObjects(self):
            # Delete any previous calculated objects
            # Make sure NOTHING is selected in the scene/object
            bpy.ops.object.select_all(action='DESELECT')
            failedNames = []
            for ob in bpy.data.objects:
                m = re.match("(Out.Material\w*|Path\w*-Path$|ErrorText|WarningSphere\w*|Out.Border\w*|Path\w*)", ob.name)
                if m:
                    try:
                        ob.select_set(True)
                        ob.hide_set(False)
                    except:
                        # maybe it's an orphaned object
                        # FAILS COVERAGE
                        failedNames.append(ob.name)
            bpy.ops.object.delete()

            if len(failedNames) > 0:
                for name in failedNames:
                    obj = bpy.data.objects[name]
                    try:
                        bpy.data.objects.remove(obj)
                    except:
                        print("DeleteCalculatedObjects cannot remove " + name)

        def GetProjectName(self):
            s = bpy.path.basename(bpy.context.blend_data.filepath)
            return s[0:-6] # Remove the '.blend'

        def GetLayerOutputFileName(self):
            if self.parent.Parameters.HasCollectionParameter("OutputFilename"):
                return self.parent.Parameters.CollectionParameter("OutputFilename")
            else:
                return ""

        #*******************************************************************************************************
        # This function will loop through the collections and produce the GCode.
        #
        # Each time it encounters a change of name in the "LayerParameters" in any collection, it will create
        # a new separate file.
        # Each time it encounters a change of cutter diameter in the "LayerParameters" in any collection, it will 
        # create a new separate file.
        # Each time it encounters a depth image in any collection, it will create 4 new separate files.
        #
        # Format of filenames:
        #                                                 { Layer Name           }
        #                                                 {     OR               }
        #   { Project File Name     }                     { Layer Name-Lx-y      }
        #   {        OR             }                     {     OR               }
        #   { Global Parameter Name } _ { Seq. Number } _ { Collection Name-Lx-y } .ngc
        #*******************************************************************************************************
#        def GetGCode4Collections(self, gcodePreAmble, gcodePostAmble):
#            curCutter = -1
#            listOfLists = []
#            listVisualPaths = []

#            # Get the name of this project (may be overridden by the global outputfilename parameter)
#            print("globals=", self.parent.Parameters.globalParams)
#            if self.parent.Parameters.HasGlobalParameter("OutputFilename"):
#                self.globalFileName = self.parent.Parameters.Global("OutputFilename")
#            else:
#                self.globalFileName = self.GetProjectName()
#            print("Processing Project", self.GetProjectName(), "as", self.globalFileName)

#            lastOp = ""
#            emptyProg = True
#            firstTime = True
#            prevCollection = ""

#            # Loop through active collections at the top level in order
#            for collNdx in bpy.context.scene.collection.children:
#                # Get current collection
#                collection = collNdx
#                
#                # We skip "Collection 0 Globals", and any invisible collections
#                if collection.name == "Collection 0 Globals":
#                    continue
#                if not self.IsCollectionVisible(collection.name):
#                    continue
#                print("Processing Collection", collection.name)
#                
#                # Remember what the PREVIOUS collection was (if any) in case we are going to write
#                # out what we have done so far
#                if firstTime:
#                    prevFName = ""
#                else:
#                    prevFName = self.layerFileName

#                # Get layer parameters
#                self.parent.Parameters.SetCollectionParameters(collection)

#                # Get the Layer file name (if any)
#                self.layerFileName = self.GetLayerOutputFileName()
#                print("self.layerFileName=", self.layerFileName)
#                    
#                # Check if we have moved onto a new collection with a different specified name
#                print("A37 1=", self.layerFileName, prevFName, firstTime)
#                if (self.layerFileName != prevFName) and (not firstTime):
#                    # We are writing out the operations because the collection has changed, 
#                    # we want to use the PREVIOUS layer file name
#                    self.layerFileName = prevFName
#                    if len(listVisualPaths) > 0:
#                        listOfLists.append(listVisualPaths)
#                        if (lastOp == "DepthImage"):
#                            listOfLists.append([])
#                            listOfLists.append([])
#                            listOfLists.append([])
#                            lastOp = ""
#                    listVisualPaths = []

#                    # In some cases, a collection only contains an image - in which there really are no
#                    # operations to write out
#                    print("A37 2=", emptyProg)
#                    if not emptyProg:
#                        s = self.globalFileName + "_" + str(self.progNumber) + "_"
#                        print("A37 3=", self.layerFileName)
#                        if self.layerFileName == "":
#                            # We are writing out the operations because the collection has changed, if there is no
#                            # specified layer file name then we want to use the PREVIOUS collection name
#                            A37
#                            s += prevCollection
#                        else:
#                            s += self.layerFileName
#                        print("Writing GCode", s)
#                        self.FinishAndWriteProgram(s)
#                        self.listPrograms += [s + ".ngc"]
#                        self.listProgramsCutter += [curCutter]
#                        # We move onto the next number in the sequence
#                        self.progNumber += 1                

#                    # Start up a new program of operations
#                    self.ss = self.GetProgramHeader(gcodePreAmble)
#                    curCutter = dia
#                    emptyProg = True

#                    # Get the Layer file name (if any)
#                    self.layerFileName = self.GetLayerOutputFileName()
#                # END OF Check if we have moved onto a new collection with a different specified name

#                firstTime = False

#                listOps = self.GetListOfOperations(collection)
#                listOps.sort()
#                opsInThisCollection = False
#                for sss in listOps:
#                    # Look for parameters for this pocket
#                    self.parent.Parameters.SetLocalParameters(sss)

#                    endDepth = self.parent.Parameters.LocalOrGlobal("EndDepth")
#                    startDepth = self.parent.Parameters.LocalOrGlobal("StartDepth")
#                    
#                    # Check if we need to start a new program
#                    # Detect if the cutter is changing or if we are doing (or have done) a depth image
#                    dia = self.parent.Parameters.LocalOrGlobal("Diameter")
#                    newProgram = False
#                    if curCutter == -1:
#                        curCutter = dia
#                    else:
#                        if (curCutter != dia) or (self.parent.IsObjectNamed(sss, "DepthImage")) or (lastOp == "DepthImage"):
#                            if len(listVisualPaths) > 0:
#                                listOfLists.append(listVisualPaths)
#                                if (lastOp == "DepthImage"):
#                                    listOfLists.append([])
#                                    listOfLists.append([])
#                                    listOfLists.append([])
#                                    lastOp = ""
#                            listVisualPaths = []

#                            if not emptyProg:
#                                s = self.globalFileName + "_" + str(self.progNumber) + "_"
#                                if self.layerFileName == "":
#                                    if opsInThisCollection:
#                                        s += collection.name
#                                        opsInThisCollection = False
#                                    else:
#                                        A75
#                                        s += prevCollection
#                                else:
#                                    A76
#                                    s += self.layerFileName
#                                print("Writing GCode", s)
#                                self.FinishAndWriteProgram(s)
#                                self.listPrograms += [s + ".ngc"]
#                                self.listProgramsCutter += [curCutter]
#                                self.progNumber += 1                
#                            self.ss = self.GetProgramHeader(gcodePreAmble)
#                            curCutter = dia
#                            emptyProg = True
#                    # END Detect if the cutter is changing

#                    # Call the pocket function
#                    self.ss += [" "]
#                    self.ss += ["(" + sss + ")"]
#                    # Check if any local parameters override speed, finishing etc.

#                    vPoly = None

#                    # Make sure all scaling transforms are applied, else can get math errors too easily                
#    #                self.UnselectAllObjects()
#                   # Make sure NOTHING is selected in the scene/object
#                    bpy.ops.object.select_all(action='DESELECT')
#                    bpy.data.objects[sss].select_set(state=True)
#                    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
#            
#                    if self.parent.IsObjectNamed(sss, "DepthImage"):
#                        # Handle Depth Image
#                        i2g = Blender4CNC.Im2GCodeSettings()
#                        obj = bpy.data.objects[sss]
#                        if bpy.context.scene.unit_settings.system == "IMPERIAL":
#                            i2g.carving_width = obj.dimensions.x * Blender4CNC.METERS_TO_INCHES
#                            i2g.carving_height = obj.dimensions.y * Blender4CNC.METERS_TO_INCHES
#                            i2g.offset_x = obj.location.x * Blender4CNC.METERS_TO_INCHES
#                            i2g.offset_y = obj.location.y * Blender4CNC.METERS_TO_INCHES
#                            i2g.carving_width = round(i2g.carving_width, 5)
#                            i2g.offset_x = round(i2g.offset_x, 5)
#                            i2g.offset_y = round(i2g.offset_y, 5)
#                        else:
#                            A102
#                            i2g.carving_width = obj.dimensions.x
#                            i2g.carving_height = obj.dimensions.y
#                            i2g.offset_x = obj.location.x
#                            i2g.offset_y = obj.location.y

#                        i2g.rough_dia = self.parent.Parameters.LocalOrGlobal("RoughDiameter")
#                        i2g.final_dia = self.parent.Parameters.LocalOrGlobal("Diameter")
#                        i2g.carve_dia = 0
#                        i2g.ystep = self.parent.Parameters.LocalOrGlobal("YStep")
#                        i2g.zstep = self.parent.Parameters.LocalOrGlobal("ZStep")
#                        i2g.max_depth = self.parent.Parameters.LocalOrGlobal("EndDepth")
#                        i2g.rapid_height = self.parent.Parameters.LocalOrGlobal("SafeZ")
#                        i2g.cutting_speed = self.parent.Parameters.LocalOrGlobal("Speed")
#                        i2g.acceleration = 1.0
#                        i2g.rapid_speed = 1.0
#                        i2g.number_layers = 1
#                        i2g.laminate_thickness = 1.0
#                        i2g.layers_grid = [[0,1]]
#                        if Blender4CNC.DEBUG_DEPTH_IMAGES:
#                            # FAILS COVERAGE
#                            i2g.clean_up = "no"
#                        else:
#                            i2g.clean_up = "yes"
#                        i2g.imagemagick_path = ""

#                        # Get the image from the material of the object
#                        # Get its first material slot
#                        material = obj.material_slots[0].material
#                        # Get the nodes in the node tree
#                        nodes = material.node_tree.nodes
#                        # Get a principled node
#                        principled = next(n for n in nodes if n.type == 'BSDF_PRINCIPLED')
#                        # Get the slot for 'base color'
#                        base_color = principled.inputs['Base Color'] #Or principled.inputs[0]

#                        # Get the link
#                        link = base_color.links[0]
#                        link_node = link.from_node

#                        ThisPath = bpy.path.abspath("//")
#                        i2g.file_name = ThisPath + link_node.image.name
#                        i2g.gcodePreAmble = gcodePreAmble
#                        i2g.gcodePostAmble = gcodePostAmble

#                        ThisPath = bpy.path.abspath("//")
#                        ThisFile = bpy.path.basename(bpy.context.blend_data.filepath)
#                        ThisFile = ThisFile[0:-6] # Remove the '.blend'

#                        i2g.outBaseName = ThisPath + self.globalFileName + "_" + str(self.progNumber) + "_"
#                        if self.layerFileName == "":
#                            i2g.outBaseName += collection.name
#                        else:
#                            A139
#                            i2g.outBaseName += self.layerFileName

#                        image = bpy.data.images[link_node.image.name]
#                        image.filepath_raw = "//" + link_node.image.name
#                        image.file_format = 'PNG'
#                        image.save()
#                                            
#                        image2GCode = Blender4CNC.Im2GCode()
#                        imNames = image2GCode.Go_Image2GCode(i2g)
#                        self.progNumber += 1                
#    #                    self.listPrograms += imNames
#                        for name in imNames:
#                            name = bpy.path.basename(name)
#    #                        name = name[0:-6]
#                            self.listPrograms.append(name)
#                        for i in range(0,int(len(imNames)/4)):
#                            self.listProgramsCutter += [i2g.rough_dia]
#                            self.listProgramsCutter += [i2g.final_dia]
#                            self.listProgramsCutter += [i2g.final_dia]
#                            self.listProgramsCutter += [i2g.final_dia]
#                        vPoly = self.parent.VisualPoly(sss, dia)
#                        vPoly.SetCoords()
##                        if (bpy.context.scene.unit_settings.system == "METRIC"):
##                            vPoly.endDepth = endDepth * 0.001
##                        else:
#                        vPoly.endDepth = endDepth
#                        #print ("  Valid " + vPoly.name + " (Depth Image)")
#                        co = vPoly.coords[0]
#                        #print ("    " + "%d points at: (%4.3f, %4.3f, %4.3f)" % (len(vPoly.indices[1]),co[0],co[1],co[2]))
#                        lastOp = "DepthImage"
#                    else:
#                        emptyProg = False
#                        opsInThisCollection = True

#                        (isOK, vPoly) = self.parent.MeshCleanup.CheckSingleMesh(bpy.data.objects[sss], dia, temp4ExpandShrink=True)
#                        if not isOK:
#                            raise Exception("Please fix potential warning points.\n(Points too close?)", (0,0))

#                        try:
#                            vPoly = self.parent.VisualPoly(sss, dia)
#                            vPoly.SetCoords()
#                        except Blender4CNC.PolyException as err:
#                            A168
#                            ob = bpy.data.objects[sss]
#                            self.Errors.ShowErrorOnOperation(ob, err.args[0])
#                            raise err
#                        except Exception as err2:
#                            A171
#                            ob = bpy.data.objects[sss]
#                            self.Errors.ShowErrorOnOperation(ob, err2.args[0])
#                            raise err2

#                        if vPoly != None:
#                            vPoly.endDepth = endDepth
#                            #print ("  Valid " + vPoly.name + " indices = " + str(vPoly.indices[1]))
#                            co = vPoly.coords[0]
#                            #print ("    " + "%d points at: (%4.3f, %4.3f, %4.3f)" % (len(vPoly.indices[1]),co[0],co[1],co[2]))

#                            if vPoly.IsNamed2("Pocket"):
#                                tenons = self.GetChildTenonsAsStrings(sss)
#                                vPoly.AddTenonsToPocket(tenons)

#                            finSpd = self.parent.Parameters.LocalOrGlobal("FinishSpeed")
#                            finAmt = self.parent.Parameters.LocalOrGlobal("FinishAmount")
#                            fin = self.parent.Parameters.LocalOrGlobal("Finishing")
#                            finBot = self.parent.Parameters.LocalOrGlobal("FinishingBottom")
#                            pDia = self.parent.Parameters.LocalOrGlobal("Diameter")
#                            pZStep = self.parent.Parameters.LocalOrGlobal("ZStep")
#                            pStepover = self.parent.Parameters.LocalOrGlobal("StepOver")
#                            pSafeZ = self.parent.Parameters.LocalOrGlobal("SafeZ")
#                            pSpd = self.parent.Parameters.LocalOrGlobal("Speed")

#                            p2g2 = Blender4CNC.Pockets(finSpd, finAmt, fin, finBot, 1, pDia, pZStep, pStepover, 0, pSafeZ, pSpd)

#                            if vPoly.IsNamed2("Pocket") and vPoly.IsCircle() and (len(vPoly.tenons)==0):
#                                l2 = p2g2.CutCircularPocket(vPoly.cx, vPoly.cy, vPoly.r, startDepth, endDepth, self.parent.Parameters.LocalOrGlobal("Finishing"))
#                                self.ss += l2
#                            elif vPoly.IsNamed2("Pocket"):
#                                listOfTenons = ""
#                                if len(tenons) > 0:
#                                    listOfTenons = []
#                                    for i in range(0,len(tenons)):
#                                        vPoly2 = self.parent.VisualPoly(tenons[i], dia)
#                                        vPoly2.SetCoords()
#                                        listOfTenons += [vPoly2.coords2]
#                                    self.ss += p2g2.CutPocket(vPoly.coords2, startDepth, endDepth, 0, listOfTenons)
#                                else:
#                                    self.ss += p2g2.CutPocket(vPoly.coords2, startDepth, endDepth, 0, [])
#                            elif vPoly.IsNamed2("Path") and vPoly.IsCircle():
#                                self.ss += p2g2.CutCircle(vPoly.coords[1][3], vPoly.coords[1][4], vPoly.r, startDepth, endDepth)
#                            elif vPoly.IsNamed2("Path") or vPoly.IsNamed2("Hole"):
#                                self.ss += p2g2.CutShapeLine(vPoly.coords2, startDepth, endDepth)
#                            elif vPoly.IsNamed2("DrillPath"):
#                                try:
#                                    fastPeck = self.Parameters.LocalOrGlobal("FastPeck")
#                                except:
#                                    fastPeck = False
#                                try:
#                                    slowPeck = self.Parameters.LocalOrGlobal("SlowPeck")
#                                except:
#                                    slowPeck = False
#                                try:
#                                    peckDepth = self.Parameters.LocalOrGlobal("PeckDepth")
#                                except:
#                                    if fastPeck or slowPeck:
#                                        raise Exception("Cannot find peck depth for drill cycle", (vPoly.poly.points[0].x, vPoly.poly.points[0].y))
#                                    else:
#                                        peckDepth = 0
#                                self.ss += p2g2.DrillCycle(vPoly.coords2, slowPeck, fastPeck, peckDepth, endDepth)
#                        lastOp = ""
#                                
#                    if vPoly != None:
#                        listVisualPaths.append(vPoly)

#                # END looping through operations                    
#                prevCollection = collection.name
#                
#            if len(listVisualPaths) > 0:
#                listOfLists.append(listVisualPaths)

#            if (lastOp == "DepthImage"):
#                A223
#                listOfLists.append([])
#                listOfLists.append([])
#                listOfLists.append([])

#            if not emptyProg:
#                s = self.globalFileName + "_" + str(self.progNumber) + "_"
#                if self.layerFileName == "":
#                    s += collection.name
#                else:
#                    s += self.layerFileName
#                self.FinishAndWriteProgram(s)
#                self.listPrograms += [s + ".ngc"]
#                self.listProgramsCutter += [curCutter]
#    #        for i in range(0, len(self.listProgramsCutter)):
#    #            print("Cutter = ", str(self.listProgramsCutter[i]) + ", " + self.listPrograms[i])
#                
#                
#            return listOfLists
        
        # Determine the ordering of collections and operations and the filenames for all
        def GetFileOrder(self):
            curCutter = -1
            progNumber = 0

            # Get the name of this project (may be overridden by the global outputfilename parameter)
            if self.parent.Parameters.HasGlobalParameter("OutputFilename"):
                globalFileName = self.parent.Parameters.Global("OutputFilename")
            else:
                globalFileName = self.GetProjectName()

            # Get a list of collections to process
            collections = []
            for collection in bpy.context.scene.collection.children:
                # We skip "Collection 0 Globals", and any invisible collections
                if collection.name == "Collection 0 Globals":
                    continue
                if not self.IsCollectionVisible(collection.name):
                    continue
                collections.append(collection)

            currentFilename = globalFileName
            collsAndOps = []

            # Loop through active collections at the top level in order
            for collection in collections:
#                print("Processing Collection", collection.name)
                
                # Get layer parameters
                self.parent.Parameters.SetCollectionParameters(collection)

                # Get the Layer file name (if any)
                self.layerFileName = self.GetLayerOutputFileName()
                if self.layerFileName != "":
                    currentFilename = self.layerFileName
                else:
                    currentFilename = globalFileName
                    
                listOps = self.GetListOfOperations(collection)
                listOps.sort()
                prevOp = ""
                for sss in listOps:
                    if self.parent.IsObjectNamed(sss, "DepthImage"):
                        progNumber += 1                
                        prevOp = "DepthImage"
                    else:
                        # Look for parameters for this operation
                        self.parent.Parameters.SetLocalParameters(sss)
                        # Detect if the cutter is changing 
                        dia = self.parent.Parameters.LocalOrGlobal("Diameter")
                        if (curCutter != dia) or (prevOp == "DepthImage"):
                            progNumber += 1   
                            curCutter = dia             
                        prevOp = ""
                    filename = currentFilename + "_" + str(progNumber)
                    collsAndOps.append((filename, collection, sss))
#            print("collsAndOps=")  
#            for collOp in collsAndOps:
#                print("collOp=", collOp)
            return collsAndOps
        def GetGCode4DepthImage(self, sss, currentFilename, gcodePreAmble, gcodePostAmble):
            print("GetGCode4DepthImage currentFilename=", currentFilename)
            # Look for parameters for this pocket
            self.parent.Parameters.SetLocalParameters(sss)
            dia = self.parent.Parameters.LocalOrGlobal("Diameter")
            # Handle Depth Image
            i2g = Blender4CNC.Im2GCodeSettings()
            obj = bpy.data.objects[sss]
            if bpy.context.scene.unit_settings.system == "IMPERIAL":
                i2g.carving_width = obj.dimensions.x * Blender4CNC.METERS_TO_INCHES
                i2g.carving_height = obj.dimensions.y * Blender4CNC.METERS_TO_INCHES
                i2g.offset_x = obj.location.x * Blender4CNC.METERS_TO_INCHES
                i2g.offset_y = obj.location.y * Blender4CNC.METERS_TO_INCHES
                i2g.carving_width = round(i2g.carving_width, 5)
                i2g.offset_x = round(i2g.offset_x, 5)
                i2g.offset_y = round(i2g.offset_y, 5)
            else:
                i2g.carving_width = obj.dimensions.x
                i2g.carving_height = obj.dimensions.y
                i2g.offset_x = obj.location.x
                i2g.offset_y = obj.location.y

            i2g.rough_dia = self.parent.Parameters.LocalOrGlobal("RoughDiameter")
            i2g.final_dia = self.parent.Parameters.LocalOrGlobal("Diameter")
            i2g.carve_dia = 0
            i2g.ystep = self.parent.Parameters.LocalOrGlobal("YStep")
            i2g.zstep = self.parent.Parameters.LocalOrGlobal("ZStep")
            i2g.max_depth = self.parent.Parameters.LocalOrGlobal("EndDepth")
            i2g.rapid_height = self.parent.Parameters.LocalOrGlobal("SafeZ")
            i2g.cutting_speed = self.parent.Parameters.LocalOrGlobal("Speed")
            i2g.acceleration = 1.0
            i2g.rapid_speed = 1.0
            i2g.number_layers = 1
            i2g.laminate_thickness = 1.0
            i2g.layers_grid = [[0,1]]
            if Blender4CNC.DEBUG_DEPTH_IMAGES:
                # FAILS COVERAGE
                i2g.clean_up = "no"
            else:
                i2g.clean_up = "yes"
            i2g.imagemagick_path = ""

            if (bpy.context.scene.unit_settings.system == "METRIC"):
                dia /= 1000
                i2g.rough_dia /= 1000
                i2g.final_dia /= 1000
                i2g.carve_dia /= 1000
                i2g.ystep /= 1000
                i2g.zstep /= 1000
                i2g.max_depth /= 1000
                i2g.rapid_height /= 1000
                
            # Get the image from the material of the object
            # Get its first material slot
            material = obj.material_slots[0].material
            # Get the nodes in the node tree
            nodes = material.node_tree.nodes
            # Get a principled node
            principled = next(n for n in nodes if n.type == 'BSDF_PRINCIPLED')
            # Get the slot for 'base color'
            base_color = principled.inputs['Base Color'] #Or principled.inputs[0]

            # Get the link
            link = base_color.links[0]
            link_node = link.from_node

            ThisPath = bpy.path.abspath("//")
            i2g.file_name = ThisPath + link_node.image.name
            i2g.gcodePreAmble = gcodePreAmble
            i2g.gcodePostAmble = gcodePostAmble

            ThisPath = bpy.path.abspath("//")
            ThisFile = bpy.path.basename(bpy.context.blend_data.filepath)
            ThisFile = ThisFile[0:-6] # Remove the '.blend'

            i2g.outBaseName = ThisPath + currentFilename

            image = bpy.data.images[link_node.image.name]
            image.filepath_raw = "//" + link_node.image.name
            image.file_format = 'PNG'
            image.save()
                                
            image2GCode = Blender4CNC.Im2GCode()
            print("GetGCode4DepthImage about to call Go_Image2GCode")
            imNames = image2GCode.Go_Image2GCode(i2g)
            print("GetGCode4DepthImage finished Go_Image2GCode")
            return (imNames, i2g)
        def GetGCode4Operation(self, sss, currentFilename):
            # Look for parameters for this pocket
            self.parent.Parameters.SetLocalParameters(sss)
            endDepth = self.parent.Parameters.LocalOrGlobal("EndDepth")
            startDepth = self.parent.Parameters.LocalOrGlobal("StartDepth")
            dia = self.parent.Parameters.LocalOrGlobal("Diameter")
            
            if (bpy.context.scene.unit_settings.system == "METRIC"):
                # Convert mm to meters
                endDepth /= 1000
                startDepth /= 1000
                dia /= 1000

            (isOK, vPoly) = self.parent.MeshCleanup.CheckSingleMesh(bpy.data.objects[sss], dia, temp4ExpandShrink=True)
            if not isOK:
                raise Exception("Please fix potential warning points.\n(Points too close?)", (0,0))

            vPoly = self.parent.VisualPoly(sss, dia)
            vPoly.SetCoords()
            # I think CheckSingleMesh catches anything
            #try:
            #    vPoly = self.parent.VisualPoly(sss, dia)
            #    vPoly.SetCoords()
            #except Blender4CNC.PolyException as err:
            #    ob = bpy.data.objects[sss]
            #    self.Errors.ShowErrorOnOperation(ob, err.args[0])
            #    raise err
            #except Exception as err2:
            #    ob = bpy.data.objects[sss]
            #    self.Errors.ShowErrorOnOperation(ob, err2.args[0])
            #    raise err2

            if vPoly != None:
                vPoly.endDepth = endDepth
                #print ("  Valid " + vPoly.name + " indices = " + str(vPoly.indices[1]))
                co = vPoly.coords[0]
                #print ("    " + "%d points at: (%4.3f, %4.3f, %4.3f)" % (len(vPoly.indices[1]),co[0],co[1],co[2]))

                if vPoly.IsNamed2("Pocket"):
                    tenons = self.GetChildTenonsAsStrings(sss)
                    vPoly.AddTenonsToPocket(tenons)

                finSpd = self.parent.Parameters.LocalOrGlobal("FinishSpeed")
                finAmt = self.parent.Parameters.LocalOrGlobal("FinishAmount")
                fin = self.parent.Parameters.LocalOrGlobal("Finishing")
                finBot = self.parent.Parameters.LocalOrGlobal("FinishingBottom")
                pDia = self.parent.Parameters.LocalOrGlobal("Diameter")
                pZStep = self.parent.Parameters.LocalOrGlobal("ZStep")
                pStepover = self.parent.Parameters.LocalOrGlobal("StepOver")
                pSafeZ = self.parent.Parameters.LocalOrGlobal("SafeZ")
                pSpd = self.parent.Parameters.LocalOrGlobal("Speed")

                if (bpy.context.scene.unit_settings.system == "METRIC"):
                    finAmt /= 1000
                    pDia /= 1000
                    pZStep /= 1000
                    pSafeZ /= 1000

                p2g2 = Blender4CNC.Pockets(finSpd, finAmt, fin, finBot, 1, pDia, pZStep, pStepover, 0, pSafeZ, pSpd)

                if vPoly.IsNamed2("Pocket") and vPoly.IsCircle() and (len(vPoly.tenons)==0):
                    l2 = p2g2.CutCircularPocket(vPoly.cx, vPoly.cy, vPoly.r, startDepth, endDepth, self.parent.Parameters.LocalOrGlobal("Finishing"))
                    self.ss += l2
                elif vPoly.IsNamed2("Pocket"):
                    listOfTenons = ""
                    if len(tenons) > 0:
                        listOfTenons = []
                        for i in range(0,len(tenons)):
                            vPoly2 = self.parent.VisualPoly(tenons[i], dia)
                            vPoly2.SetCoords()
                            listOfTenons += [vPoly2.coords2]
                        self.ss += p2g2.CutPocket(vPoly.coords2, startDepth, endDepth, 0, listOfTenons)
                    else:
                        self.ss += p2g2.CutPocket(vPoly.coords2, startDepth, endDepth, 0, [])
                elif vPoly.IsNamed2("Path") and vPoly.IsCircle():
                    self.ss += p2g2.CutCircle(vPoly.coords[1][3], vPoly.coords[1][4], vPoly.r, startDepth, endDepth)
                elif vPoly.IsNamed2("Path") or vPoly.IsNamed2("Hole"):
                    self.ss += p2g2.CutShapeLine(vPoly.coords2, startDepth, endDepth)
                elif vPoly.IsNamed2("DrillPath"):
                    try:
                        fastPeck = self.parent.Parameters.LocalOrGlobal("FastPeck")
                    except:
                        fastPeck = False
                    try:
                        slowPeck = self.parent.Parameters.LocalOrGlobal("SlowPeck")
                    except:
                        slowPeck = False
                    print("self.parent.Parameters.globalParams=", self.parent.Parameters.globalParams)
                    try:
                        peckDepth = self.parent.Parameters.LocalOrGlobal("PeckDepth")
                    except:
                        if fastPeck or slowPeck:
                            raise Exception("Cannot find peck depth for drill cycle", (vPoly.poly.points[0][0], vPoly.poly.points[0][1]))
                        else:
                            peckDepth = 0
                    print("slowPeck, fastPeck, peckDepth=", slowPeck, fastPeck, peckDepth)
                    self.ss += p2g2.DrillCycle(vPoly.coords2, slowPeck, fastPeck, peckDepth, endDepth)
            return vPoly
        def GetGCode4Collections(self, gcodePreAmble, gcodePostAmble):
            curCutter = -1
            listOfLists = []
            listVisualPaths = []
            listPrograms = []
            listProgramsCutter = []
            self.ss = []
            
            collsAndOps = self.GetFileOrder()

            # Loop through active collections at the top level in order
            for ndx in range(0,len(collsAndOps)):
                collOp = collsAndOps[ndx]
                (currentFilename, collection, sss) = collOp
#                print("currentFilename=", currentFilename)
                print("Processing Collection", collection.name)
                
                # Get layer parameters
                self.parent.Parameters.SetCollectionParameters(collection)

                # Look for parameters for this pocket
                self.parent.Parameters.SetLocalParameters(sss)

                endDepth = self.parent.Parameters.LocalOrGlobal("EndDepth")
                startDepth = self.parent.Parameters.LocalOrGlobal("StartDepth")
                    
                # Call the pocket function
                self.ss += [" "]
                self.ss += ["(" + sss + ")"]
                # Check if any local parameters override speed, finishing etc.

                vPoly = None

                # Make sure all scaling transforms are applied, else can get math errors too easily                
                # Make sure NOTHING is selected in the scene/object
                bpy.ops.object.select_all(action='DESELECT')
                bpy.data.objects[sss].select_set(state=True)
                bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
        
                if self.parent.IsObjectNamed(sss, "DepthImage"):
                    (imNames, i2g) = self.GetGCode4DepthImage(sss, currentFilename, gcodePreAmble, gcodePostAmble)
                    for name in imNames:
                        name = bpy.path.basename(name)
                        self.listPrograms.append(name)
                    for i in range(0,int(len(imNames)/4)):
                        self.listProgramsCutter += [i2g.rough_dia]
                        self.listProgramsCutter += [i2g.final_dia]
                        self.listProgramsCutter += [i2g.final_dia]
                        self.listProgramsCutter += [i2g.final_dia]
                    vPoly = self.parent.VisualPoly(sss, i2g.final_dia)
                    vPoly.SetCoords()
                    if (bpy.context.scene.unit_settings.system == "METRIC"):
                        vPoly.endDepth = endDepth * 0.001
                    else:
                        vPoly.endDepth = endDepth
                    #print ("  Valid " + vPoly.name + " (Depth Image)")
                    #co = vPoly.coords[0]
                    #print ("    " + "%d points at: (%4.3f, %4.3f, %4.3f)" % (len(vPoly.indices[1]),co[0],co[1],co[2]))
                else:
                    vPoly = self.GetGCode4Operation(sss, currentFilename)
                                
                if vPoly != None:
                    listVisualPaths.append(vPoly)
                    
                    if ndx == (len(collsAndOps)-1):
                        nextFilename = ""
                    else:
                        nextFilename = collsAndOps[ndx + 1][0]
                    if currentFilename != nextFilename:
                        if not self.parent.IsObjectNamed(sss, "DepthImage"):
                            print("Writing GCode", currentFilename, nextFilename)
                            self.ss = self.GetProgramHeader(gcodePreAmble) + self.ss
                            self.FinishAndWriteProgram(currentFilename)
                            self.listPrograms += [currentFilename + ".ngc"]
                            self.listProgramsCutter += [curCutter]
                            self.ss = []

                        if len(listVisualPaths) > 0:
                            listOfLists.append(listVisualPaths)
                            listVisualPaths = []
                        if self.parent.IsObjectNamed(sss, "DepthImage"):
                            listOfLists.append([])
                            listOfLists.append([])
                            listOfLists.append([])

                
#            print("listOfLists=", listOfLists)
            return listOfLists

        #*************************************************************************
        # Try to make this collection visible - may not be possible
        #*************************************************************************
        def MakeCollectionVisible(self, name):                
            viewLayers = bpy.context.view_layer.layer_collection
            if name not in viewLayers.children.keys():
                return
            if viewLayers.children[name].exclude == True:
                viewLayers.children[name].exclude = False
            viewLayers.children[name].hide_viewport = False
            return not viewLayers.children[name].exclude

        #*************************************************************************
        # Check if this collection is visible
        #*************************************************************************
        def IsCollectionVisible(self, name):                
            viewLayers = bpy.context.view_layer.layer_collection
                
            if name not in viewLayers.children.keys():
                return False
            # Exclude is the "checkmark"
            if viewLayers.children[name].exclude == True:
                return False
            # Hide_viewport is the "eye"
            if viewLayers.children[name].hide_viewport == True:
                return False
            return True

        #*************************************************************************
        # Create a collection to hold the path models
        #*************************************************************************
        def CreateCollectionOut(self):
            if "Collection Out" not in bpy.data.collections.keys():
                parent = bpy.data.collections["Collection 0 Globals"]
                new_collection = bpy.data.collections.new("Collection Out")
                parent.children.link(new_collection)
            else:
                # Clear the collection
                collOut = bpy.data.collections["Collection Out"] 
                for k in collOut.objects:
                    if k.name[0:4] == "Out.":
                        bpy.data.objects.remove(k, do_unlink=True)

        #********************************************************************
        # Finishes the current program and writes it out to disk
        #********************************************************************
        def FinishAndWriteProgram(self, fName):
            ThisPath = bpy.path.abspath("//")
            ThisFile = bpy.path.basename(bpy.context.blend_data.filepath)
            ThisFile = ThisFile[0:-6] # Remove the '.blend'
            
            fName = ThisPath + fName
            

            gcodePostAmble = self.parent.GetTextObject("GCodePostAmble")
            l2 = [""]
            l2 += gcodePostAmble
            l2.append("( Total Lines = %d )" % (len(self.ss)+1))
            self.ss += l2
            print("Finished %d Lines of GCode" % (len(self.ss)+1))

    #        self.WritePyCode(fName + ".ngc")
            with io.open(fName + ".ngc", "w") as f:
                f.write('\n'.join(self.ss))
    #        self.listPrograms += [fName + ".ngc"]

        #********************************************************************
        # 
        #********************************************************************
        def GetProgramHeader(self, gcodePreAmble):
            l = []
            # Put the Job Parameters at the top of the GCode file as a comment
            l2 = self.parent.GetTextObject("JobParameters")
            l2 = [s for s in l2 if "(" not in s]
            l2 = [s for s in l2 if ")" not in s]
            l2 = ["(" + s + ")" for s in l2]
            l2.append("")

            # Put the GCode PreAmble at the top of the GCode file
            l2 += gcodePreAmble
            l2.append(Blender4CNC.Pockets(10, 0.001, False, False, 1, 0.25, -0.1, 0.5, 0, 0.1, 20).GetSpeedGCodeStr(self.parent.Parameters.LocalOrGlobal("Speed")))
            l += l2
            
            return l
                                    
        #*************************************************************************
        # Gets a list of tenons inside a pocket
        #*************************************************************************
        def GetChildTenonsAsStrings(self, oName) :
    #        l = self.GetChildren(self.ReturnObjectByName(oName)) 
            # Return a list of the children of an object
            l = [ob_child for ob_child in bpy.data.objects if ob_child.parent == self.parent.ReturnObjectByName(oName)]
            l2 = [obj.name for obj in l if obj.name[4:9] == "Tenon"]
            # Need to check the tenons are visible
            viewLayers = bpy.context.view_layer.layer_collection
                
            l3 = []
            for name in l2:            
                ob = bpy.data.objects[name]
                if ob.visible_get():
                    l3.append(name)
            return l3

        #*************************************************************************
        # Get all pockets/paths to process, print info about them and return the list
        #*************************************************************************
        def GetListOfOperations(self, collection):
            listPockets = []
            for ob in collection.objects:
                if ob.type != 'MESH':
                    continue
                if (self.parent.IsObjectNamed(ob.name, "DepthImage") or self.parent.IsObjectNamed(ob.name, "Pocket") or self.parent.IsObjectNamed(ob.name, "Path") or self.parent.IsObjectNamed(ob.name, "Hole") or self.parent.IsObjectNamed(ob.name, "DrillPath")):
                    if ob.visible_get():
                        listPockets.append(ob.name)
                            
            return listPockets

#END_COVERAGE#

    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    # A class to vizualize everything
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    #OVERAGE_CLASS VizualizeCollections
    class VizualizeCollections:
    
        def __init__(self, par, lPrograms):
            self.parent = par
            self.listPrograms = lPrograms

        #*************************************************************************
        #
        #*************************************************************************
        def VizualizeCollections(self, listOfLists):
#            gcodePathViewer = self.GCodePathViewer()
            gcodePathViewer = Blender4CNC.GCodePathViewer()

            # Create some materials if they do not already exist in the blender project
            mats = {}
            mats["Blue"] = self.MakeMaterial('Blue', (0,0,1,1), (1,1,1), 1)
            mats["Red"] = self.MakeMaterial('Red', (1,0,0,1), (1,1,1), 1)
            mats["Green"] = self.MakeMaterial('Green', (0,1,0,1), (1,1,1), 1)
            mats["Yellow"] = self.MakeMaterial('Yellow', (1,1,0,1), (1,1,1), 1)
            mats["Cyan"] = self.MakeMaterial('Cyan', (0,1,1,1), (1,1,1), 1)
            mats["Magenta"] = self.MakeMaterial('Magenta', (1,0,1,1), (1,1,1), 1)
            
            if "Color4ResultPaths" in bpy.data.materials.keys():
                pathMat = bpy.data.materials["Color4ResultPaths"]
            else:
                pathMat = mats["Red"]
        
            if "MaterialBlank" not in bpy.data.objects.keys():
                raise Exception("Cannot find the material blank 'MaterialBlank' object.", (0,0))
            blankSize = bpy.data.objects["MaterialBlank"].dimensions
            
    #        self.UnselectAllObjects()
            # Make sure NOTHING is selected in the scene/object
            bpy.ops.object.select_all(action='DESELECT')
            bpy.data.objects["MaterialBlank"].select_set(state=True)
            bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)

            listOfListsTotal = []
            #print("self.listPrograms")
            #print(self.listPrograms)
            #print("listOfLists")
            #print(listOfLists)
#            print("listOfLists in Viz, before loop=", listOfLists)
#            print("self.listPrograms in Viz, before loop=", self.listPrograms)
            for i in range(0, len(self.listPrograms)):
                # Run the python program to create the GCode file
                variables = {}

                # Expand any drill cycles into a list of holes
                curList = listOfLists[i]
                ii = 0
                drillPolys = []
                while ii < len(curList):
                    vPoly = curList[ii]
                    if vPoly.IsNamed2("DrillPath"):
                        nameParts = vPoly.name.split('.')
                        for pointI in range(0, len(vPoly.coords2)):
                            newName = nameParts[0] + ".Hole." + nameParts[1] + "." + nameParts[2] + "-" + str(pointI)
                            vPoly2 = Blender4CNC.VisualPoly(newName, vPoly.dia)
                            vPoly2.SetCoords([vPoly.coords2[pointI]])
                            vPoly2.endDepth = vPoly.endDepth
                            drillPolys.append(vPoly2)
                        curList.pop(ii)
                    else:
                        ii += 1
                curList += drillPolys
                listOfLists[i] = curList
#                print("curList=", curList)
                        

                # Create all the paths in the material for this program
                listOfListsTotal += listOfLists[i]

                # Join together any close touching tenons in the poly (only for pockets)
                for vPoly in listOfListsTotal:
                    vPoly.JoinOverlappingVisualTenons()
                # Join together any close touching tenons in the poly (only for pockets)
                for vPoly in listOfListsTotal:
                    # Reduce a list of lists of tenons to just a list of tenons
#                    print("vPoly.tenons=", vPoly.tenons)
                    l2 = []
                    for x in vPoly.tenons:
#                        print("l2=", l2)
#                        print("x=", x)
                        if type(x) == list:
                            l2 += x
                        else:
                            l2.append(x)
                    vPoly.tenons = l2
                # if any tenons are touching the main outer edge,join them to it (only for pockets)
                for vPoly in listOfListsTotal:
                    vPoly.JoinOverlappingVisualTenonsToPoly()

                # 3 of the 4 "vPoly lists" for depth images are empty
    #            if len(listOfLists[i]) != 0:
                print("Visualizing", str(len(listOfListsTotal)), "polys.")
                #print("listOfLists[i][0].poly=", listOfLists[i][0].poly)
                #for i2 in range(0,len(listOfLists)):
                #    if type(listOfLists[i]) == list:
                #        listOfLists[i] = [listOfLists[i][0]]
                #print("listOfLists[i]=", listOfLists[i])
                #print("listOfLists[i][0].poly=", listOfLists[i][0].poly)
                #print("listOfLists[i][0].tenons=", listOfLists[i][0].tenons)
                #print("listOfLists[i][1].tenons=", listOfLists[i][1].tenons)
                self.CreateVisualPolysInMaterial(listOfLists[i], "Out.Material", blankSize.y * (i+1), i, None, blankSize, listOfListsTotal)
                print("Visualizing", str(len(listOfListsTotal)), "polys - Done.")

                # Create a path for the GCode
                nameStr = self.listPrograms[i]
                folder = os.path.dirname(nameStr)
                filenameNoExt = folder + os.path.sep + os.path.basename(nameStr).split('.')[0]
                filename = filenameNoExt + ".ngc"

                scale = 1
                if bpy.context.scene.unit_settings.system == "IMPERIAL":
                    scale = Blender4CNC.INCHES_TO_METERS
                else:
                    scale = 0.001

                folder = os.path.dirname(bpy.context.blend_data.filepath)
                filename = folder + os.path.sep + nameStr.split('.')[0] + ".ngc"

                gcodePathViewer.VisualizeGCodePath("Path" + str(i), pathMat, filename, True, float(self.parent.Parameters.ProjectParameter("PathBevelDepth")), scale)
    #            cProfile.runctx('gcodePathViewer.VisualizeGCodePath("Path" + str(i), pathMat, filename, True, float(self.projectParams["PathBevelDepth"]), scale)', globals(), locals())

                obj = bpy.data.objects["Path" + str(i)]
                
                obj.location = (0,-blankSize.y*(i+1), float(self.parent.Parameters.ProjectParameter("PathZOffset")) )
                
            # Clear the collection of any remaining temporary paths
            collOut = bpy.data.collections["Collection Out"] 
            for k in collOut.objects:
    #            if k.name[0:10] != "Out.Border":
    #                bpy.data.objects.remove(k, do_unlink=True)
    #            if k.name[0:4] != "Test":
    #                bpy.data.objects.remove(k, do_unlink=True)
                if k.name[0:12] != "Out.Material":
                    bpy.data.objects.remove(k, do_unlink=True)

            # Cleanup temporary files
            self.DeleteFiles("Final*.png")
            self.DeleteFiles("Temp*.png")
            
            # Make sure NOTHING is selected in the scene/object
            bpy.ops.object.select_all(action='DESELECT')
    #        self.UnselectAllObjects()

        #**************************************************************************
        # Create a material in Blender
        #**************************************************************************
        def MakeMaterial(self, name, diffuse, specular, alpha):
            mat = bpy.data.materials.get(name)
            if mat is None:
                mat = bpy.data.materials.new(name)
                mat.diffuse_color = diffuse
                #mat.diffuse_shader = 'LAMBERT' 
                #mat.diffuse_intensity = 1.0 
                mat.specular_color = specular
                #mat.specular_shader = 'COOKTORR'
                mat.specular_intensity = 0.5
                #mat.alpha = alpha
                #mat.ambient = 1
            return mat

        #*************************************************************************
        def CreateVisualPolyMeshesWalls_CSG(self, listVisualPaths, tempName, dims, blankSize, listOfObjects):   
            blankX = blankSize.x             

            for i in range(0,len(listVisualPaths)):
                vPoly = listVisualPaths[i]
                if (bpy.context.scene.unit_settings.system == "METRIC"):
#                    endDepth = vPoly.endDepth * 0.001
                    endDepth = vPoly.endDepth
                else:
                    endDepth = vPoly.endDepth
                print("CreateVisualPolyMeshesWalls_CSG endDepth=", endDepth)
                obj = listOfObjects[i]
                objPoly = obj[0]
                objTenons = obj[1]

                endDepth2 = endDepth
                if bpy.context.scene.unit_settings.system == "IMPERIAL":
                    endDepth2 = endDepth * Blender4CNC.INCHES_TO_METERS

                self.ExtrudePolyObject(objPoly, endDepth2)
                for objTenon in objTenons:
                    self.ExtrudePolyObject(objTenon, endDepth*1.01)
            
        #*************************************************************************
        # Convert a Blender object into a CSG object
        #*************************************************************************
        def ConvertObjectToCSG(self, name):
            bpy.ops.object.select_all(action='DESELECT') # Deselect all objects
            obj = bpy.data.objects[name]
            obj.select_set(state=True)
    #        self.MakeThisObjectTheActiveObject(obj)
            # Make object the active object in the scene
            bpy.context.view_layer.objects.active = obj
            # Enter edit mode
            bpy.ops.object.editmode_toggle()
            try:
                bm = bmesh.from_edit_mesh(obj.data)
                polys = []
                count = 0
                for face in bm.faces:
                    verts2 = []
                    vertsTest = []
                    # THE CSG CODE HAS AN ISSUE WITH REMOVING SMALL/THIN TRIANGLES ?
                    # So convert meters to millimeters so that vertices like 0.005 become 5
                    # THIS IS TEMPORARY - LATER, MAKE WHATEVER CSG DOES BE RELATIVE AND SCALABLE
                    if bpy.context.scene.unit_settings.system in ["METRIC"]:
                        for v in face.verts:
                            verts2.append((v.co.x * 1000, v.co.y * 1000, v.co.z * 1000))
                    elif bpy.context.scene.unit_settings.system in ["IMPERIAL"]:
                        for v in face.verts:
                            verts2.append((v.co.x * 1000 * 25.4, v.co.y * 1000 * 25.4, v.co.z * 1000 * 25.4))
                    else:
                        for v in face.verts:
                            verts2.append((v.co.x, v.co.y, v.co.z))

                    plane = Blender4CNC.CSG.GetPlaneForVertices(verts2)
                    if plane != None:
                        poly = Blender4CNC.CSG.CSGPolygon(verts2, plane)
                        polys.append(poly)
                polys2 = polys
                #print("ConvertObjectToCSG polys2=", polys2)
                #for pl in polys2:
                #    print("ConvertObjectToCSG pl=", pl.vertices, pl.plane)
                csgObj = Blender4CNC.CSG.fromPolygons(polys2)
            finally:
                # Exit edit mode
                bpy.ops.object.editmode_toggle()
            return csgObj

        #*************************************************************************
        # 
        #*************************************************************************
        def GetPolys4CSG(self, name):
            bpy.ops.object.select_all(action='DESELECT') # Deselect all objects
            obj = bpy.data.objects[name]
            obj.select_set(state=True)
    #        self.MakeThisObjectTheActiveObject(obj)
            # Make object the active object in the scene
            bpy.context.view_layer.objects.active = obj
            # Enter edit mode
            bpy.ops.object.editmode_toggle()
            try:
                bm = bmesh.from_edit_mesh(obj.data)
                polys = []
                count = 0
                for face in bm.faces:
                    verts2 = []
                    vertsTest = []
                    # THE CSG CODE HAS AN ISSUE WITH REMOVING SMALL/THIN TRIANGLES ?
                    # So convert meters to millimeters so that vertices like 0.005 become 5
                    # THIS IS TEMPORARY - LATER, MAKE WHATEVER CSG DOES BE RELATIVE AND SCALABLE
                    if bpy.context.scene.unit_settings.system in ["METRIC"]:
                        for v in face.verts:
                            verts2.append((v.co.x * 1000, v.co.y * 1000, v.co.z * 1000))
                    elif bpy.context.scene.unit_settings.system in ["IMPERIAL"]:
                        for v in face.verts:
                            verts2.append((v.co.x * 1000 * 25.4, v.co.y * 1000 * 25.4, v.co.z * 1000 * 25.4))
                    else:
                        for v in face.verts:
                            verts2.append((v.co.x, v.co.y, v.co.z))
                    plane = Blender4CNC.CSG.GetPlaneForVertices(verts2)
                    if plane != None:
                        poly = Blender4CNC.CSG.CSGPolygon(verts2, plane)
                        polys.append(poly)
                polys2 = polys
            finally:
                # Exit edit mode
                bpy.ops.object.editmode_toggle()
            return polys2

        def CreateVisualPolysInMaterial(self, listVisualPaths, matName2, matLocY, iNum, dims, blankSize, listVisualPathsTotal):

            # Create all the "tops" of the pockets
            if len(listVisualPaths) != 0:
#                print("listVisualPaths[0]=", listVisualPaths[0])
#                print("listVisualPaths[0].tenons=", listVisualPaths[0].tenons)
                listOfObjects = self.CreateVisualPolyMeshes_CSG(listVisualPaths, dims, iNum, blankSize)
            else:
                listOfObjects = []

            # Create the walls and bottoms of pockets
            self.CreateVisualPolyMeshesWalls_CSG(listVisualPaths, "", dims, blankSize, listOfObjects)
            
            # Duplicate the material blank
            # Select the names object
            bpy.ops.object.select_all(action='DESELECT') # Deselect all objects
            if iNum == 0:
                csgObj = self.ConvertObjectToCSG("MaterialBlank")
            else:
                csgObj = self.ConvertObjectToCSG("Out.Material" + str(iNum-1))
    # TEMPORARY********************************************************************************
            verts, faces, count = csgObj.toVerticesAndPolygons()
    #        print("CreateVisualPolysInMaterial verts=", verts)
    #        print("CreateVisualPolysInMaterial faces=", faces)
    #        print("CreateVisualPolysInMaterial count=", count)
    # END TEMPORARY********************************************************************************

    #        polys = []
    #        for i in range(0,len(listOfObjects)):
    #            obj = listOfObjects[i]
    #            objPoly = obj[0]
    #            objTenons = obj[1]
    #            
    #            polys = self.GetPolys4CSG(objPoly.name)
    #            csgObj2 = Blender4CNC.CSG.fromPolygons(polys)
    #            # Must handle tenons LATER!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    #            for objTenon in objTenons:
    #                csgObj3 = self.ConvertObjectToCSG(objTenon.name)
    #                csgObj2 = csgObj2 - csgObj3
    #                
    #            csgObj = csgObj - csgObj2

            for i in range(0,len(listOfObjects)):
                obj = listOfObjects[i]
                objPoly = obj[0]
                objTenons = obj[1]
                
                polys = self.GetPolys4CSG(objPoly.name)
                if i ==0:
                    # Create the first CSG object to subtract from material
                    csgObj2Subtract = Blender4CNC.CSG.fromPolygons(polys)
                    # If it has any tenons, remove them from the volume
                    for objTenon in objTenons:
                        csgTenon = self.ConvertObjectToCSG(objTenon.name)
                        csgObj2Subtract = csgObj2Subtract - csgTenon
                else:
                    # Create the next CSG object to subtract from material
                    csgObj2Union = Blender4CNC.CSG.fromPolygons(polys)
                    # If it has any tenons, remove them from the volume
                    for objTenon in objTenons:
                        csgTenon = self.ConvertObjectToCSG(objTenon.name)
                        csgObj2Union = csgObj2Union - csgTenon
                    # We have to union objects together to handle cases of where an object is inside another
                    csgObj2Subtract = csgObj2Subtract + csgObj2Union

            if len(listVisualPaths) != 0:
                csgObj = csgObj - csgObj2Subtract

    #            polys += self.GetPolys4CSG(objPoly.name)
    #        csgObj2 = Blender4CNC.CSG.fromPolygons(polys)
    #                
    #        csgObj = csgObj - csgObj2

            verts, faces, count = csgObj.toVerticesAndPolygons()
            points3d = verts

            # THE CSG CODE HAS AN ISSUE WITH REMOVING SMALL/THIN TRIANGLES ?
            # So convert meters to millimeters so that vertices like 0.005 become 5
            # THIS IS TEMPORARY - LATER, MAKE WHATEVER CSG DOES BE RELATIVE AND SCALABLE
            if bpy.context.scene.unit_settings.system in ["METRIC"]:
                for i in range(0,len(points3d)):
                    points3d[i] = (points3d[i][0] / 1000, points3d[i][1] / 1000, points3d[i][2] / 1000)
            elif bpy.context.scene.unit_settings.system in ["IMPERIAL"]:
                for i in range(0,len(points3d)):
                    points3d[i] = (points3d[i][0] / (1000 * 25.4), points3d[i][1] / (1000 * 25.4), points3d[i][2] / (1000 * 25.4))

            # Create Blender object from CSG object and color the faces
            edges3d = []
            eSearch = {}
            for face in faces:
                for i in range(-1,len(face)-1):
                    e1 = min(face[i], face[i+1])
                    e2 = max(face[i], face[i+1])
                    key = e1 * e2 + e1 + e2
                    if key not in eSearch.keys():
                        edges3d.append([e1, e2])
                        eSearch[key] = [[e1, e2]]
                    else:                                
                        l = eSearch[key]
                        if [e1, e2] not in l:
                            edges3d.append([e1, e2])
                            eSearch[key] = l + [[e1, e2]]

            mesh_data = bpy.data.meshes.new("Test_Mesh")
    #        mesh_data.from_pydata(points3d, edges3d, faces)
    #        print("faces=", faces)
    #        print(len(faces))
    #        faces2 = faces[:600]
    #        print("faces2=", faces2)
    #        for i in range(1,len(faces)):
    #            faces2 = faces[:i]
    #            print(len(faces), i, faces2[-1])
    #            for j in faces2[-1]:
    #                print(points3d[j])
    #            mesh_data = bpy.data.meshes.new("Test_Mesh")
    #            mesh_data.from_pydata(points3d, [], faces2)
            mesh_data.from_pydata(points3d, [], faces)
            mesh_data.update()
            
            matName2 = matName2 + str(iNum)
            obj = bpy.data.objects.new(matName2, mesh_data)
            bpy.data.collections["Collection Out"].objects.link(obj)

            obj.location = Vector((63,0,0))
            obj.select_set(state=True)

            bmats = bpy.data.materials
            if "Color4ResultTop" in bmats.keys():
                mat = bmats.get("Color4ResultTop")
            else:
                mat = bpy.data.materials.get("Cyan")
            obj.data.materials.append(mat)
            if "Color4ResultBottom" in bmats.keys():
                mat = bmats.get("Color4ResultBottom")
            else:
                mat = bpy.data.materials.get("Blue")
            obj.data.materials.append(mat)
            if "Color4ResultSideWalls" in bmats.keys():
                mat = bmats.get("Color4ResultSideWalls")
            else:
                mat = bpy.data.materials.get("Red")
            obj.data.materials.append(mat)
            obj.active_material_index = 0

            count = 0
            zEqualA = [False] * len(faces)
            topPlaneA = [False] * len(faces)
            # Determine if a face is horizontal or vertical
            for face in faces:
                zEqual = True
                zz = obj.data.vertices[face[0]].co.z
                for i in range(1,len(face)):
                    zzz = obj.data.vertices[face[i]].co.z
                    zzzz = abs(zzz-zz)
                    # PRECISION ***********************************************
                    if zzzz > 0.0001:
                        zEqual = False
                        break
                if zEqual and (zz == 0):
                    topPlane = True
                else:
                    topPlane = False
                zEqualA[count] = zEqual
                topPlaneA[count] = topPlane
                count += 1
                
            me = obj.data
            count = 0
            for poly in me.polygons:
                if zEqualA[count] and topPlaneA[count]:
                    count += 1
                    continue
                if poly.select:
                    if zEqualA[count]:
                        poly.material_index = 1
                    else:
                        poly.material_index = 2
                count += 1
                
            self.RemoveDuplicateVertices(matName2)

            # Move output material to where we really want it
            bpy.ops.object.select_all(action='DESELECT') # Deselect all objects
            obj = bpy.data.objects[matName2]
            obj.select_set(state=True)
            obj.location[0] = 0
            obj.location[1] = -blankSize.y * (iNum + 1)


        # BE CAREFUL!
        # RemoveDuplicateVertices is called after creating a Blender object from the results of the CSG actions
        # (after subtracting the paths from a mseh). If we combine close vertices from two different polygons
        # it is possible that one or more polygons will no longer be truly planar - this then messes up the CSG
        # functions as the object is passed back into the next stage of processing CSG when we have multiple
        # stages (for example when we do some cuts and then a depth image - we have at least 5 stages - chances
        # are possible that by the 5th stage we have a problem. Therefore we set the threshold to be very low.
        # Actually, even when the threshold ius as small as threshold=Blender4CNC.ABS_TOLERANCE we have problems!
        def RemoveDuplicateVertices(self, objName):
            return
            # Select the names object
            bpy.ops.object.select_all(action='DESELECT') # Deselect all objects
            obj = bpy.data.objects[objName]
            obj.select_set(state=True)
            # Select all vertices
            bpy.ops.object.editmode_toggle()
            bpy.ops.mesh.select_all(action='SELECT')
            # Remove duplicate vertices
            bpy.ops.mesh.remove_doubles(threshold=Blender4CNC.ABS_TOLERANCE)
            bpy.ops.object.editmode_toggle()

        def DeleteFiles(self, names):
            try:
                for f in glob.glob(folder + os.path.sep + names):
                    os.remove(f)
            except:
                pass

        #*************************************************************************
        # Given a list of visual paths, will create these paths in a new blank
        #*************************************************************************
        def CreateMeshFromPoly_CSG(self, poly, outName, outNameMesh, loc, collName, addZ):
            points3d = []
            zOfTop = 0.005 + addZ
            if bpy.context.scene.unit_settings.system == "METRIC":
                zOfTop = (0.005 + addZ) * Blender4CNC.INCHES_TO_METERS
            elif bpy.context.scene.unit_settings.system == "IMPERIAL":
                zOfTop = (0.005 + addZ) * Blender4CNC.INCHES_TO_METERS
            else:
                zOfTop = 0.005 + addZ
            for i in range(0, len(poly.points)):
                p = poly.points[i]
                points3d += [(p[0], p[1], zOfTop)]
        
            edges3d = [[ed, ed+1] for ed in range(0,len(points3d)-1)]
            edges3d.append([len(points3d)-1,0])
            mesh_data = bpy.data.meshes.new(outName + outNameMesh)
            faces3d = []
            for i in range(0,len(points3d)):
                faces3d.append(i)
            mesh_data.from_pydata(points3d, edges3d, [faces3d])
            mesh_data.update()

            obj = bpy.data.objects.new(outName, mesh_data)
            obj.location = loc
            bpy.data.collections[collName].objects.link(obj)
            obj.select_set(state=True)
            return obj
        def CreateVisualPolyMeshes_CSG(self, listVisualPaths, dims, iNum, blankSize):                

            # Make sure nothing like the material is selected
    #        self.UnselectAllObjects()
            # Make sure NOTHING is selected in the scene/object
            bpy.ops.object.select_all(action='DESELECT')
            
            # Create approximate curves for all polys (and their tenons)
            for vPoly in listVisualPaths:
                # Just ignore tenons
                if type(vPoly.poly) == list:
                    vPoly.poly = vPoly.poly[0]
#                newList = []
#                for l2 in vPoly.tenons:
#                    newList += l2
#                vPoly.tenons = newList
#                print("listVisualPaths[0].tenons=", listVisualPaths[0].tenons)
#                print("listVisualPaths[1].tenons=", listVisualPaths[1].tenons)
                vPoly.CalcApproxCurves()

                # Due to how Blender operates with units - if a GCode path is in IMPERIAL, we
                # must scale all the coordinates because Blender is esentially metric.
                if bpy.context.scene.unit_settings.system == "IMPERIAL": 
                    # Convert from inches to meters
                    vPoly.ScaleApproxPolyAndTenons(Blender4CNC.INCHES_TO_METERS)
#                else:
#                    vPoly.ScaleApproxPolyAndTenons(0.001)
                
            blankX = blankSize.x
            
            # Create meshes
            listOfObjects = []
            for i in range(0,len(listVisualPaths)):
                vPoly = listVisualPaths[i]
                
                if vPoly.IsNamed2("Pocket") and (not vPoly.poly.PolyIsClockwise()):
                    # A CCW defined pocket is a climb-cut and needs to be reversed for faces to be correct in CSG
                    tempPoly = vPoly.approxPoly.ReverseLineDirections()
                    objPoly = self.CreateMeshFromPoly_CSG(tempPoly, vPoly.outName, vPoly.outName + "_mesh", (blankX,0,0), "Collection Out", 0)
                elif vPoly.IsNamed2("DepthImage") and (not vPoly.poly.PolyIsClockwise()):
                    # A CCW defined depth image needs to be reversed for faces to be correct in CSG
                    tempPoly = vPoly.approxPoly.ReverseLineDirections()
                    objPoly = self.CreateMeshFromPoly_CSG(tempPoly, vPoly.outName, vPoly.outName + "_mesh", (blankX,0,0), "Collection Out", 0)
                else:
                    objPoly = self.CreateMeshFromPoly_CSG(vPoly.approxPoly, vPoly.outName, vPoly.outName + "_mesh", (blankX,0,0), "Collection Out", 0)
                    
                objTenons = []
                for tenon in vPoly.approxTenons:
                    if not tenon.PolyIsClockwise():
                        revTenon = tenon.ReverseLineDirections()
                    else:
                        revTenon = tenon
                    objTenon = self.CreateMeshFromPoly_CSG(revTenon, vPoly.outName + "_tenon", vPoly.outName + "_tenon_mesh", (blankX,0,0), "Collection Out", 0.01)
                    objTenons.append(objTenon)                
                listOfObjects.append((objPoly, objTenons))
            return listOfObjects

        #*************************************************************************
        # Given an object newly created from a polytoxogon - extrudes all the 
        # edges down in the Z direction by endDepth
        # (Assumes that all points in edit mode are selected already)
        #*************************************************************************
        def ExtrudePolyObject(self, obj, endDepth):
            bpy.ops.object.select_all(action='DESELECT') # Deselect all objects
            bpy.context.view_layer.objects.active = obj
            bpy.ops.object.editmode_toggle()
    #        bpy.ops.mesh.extrude_edges_move(MESH_OT_extrude_edges_indiv={"use_normal_flip":False, "mirror":False}, TRANSFORM_OT_translate={"value":(-0, -0, endDepth), "orient_type":'GLOBAL', "orient_matrix":((1, 0, 0), (0, 1, 0), (0, 0, 1)), "orient_matrix_type":'GLOBAL', "constraint_axis":(False, False, True), "mirror":False, "use_proportional_edit":False, "proportional_edit_falloff":'SMOOTH', "proportional_size":1, "use_proportional_connected":False, "use_proportional_projected":False, "snap":False, "snap_target":'CLOSEST', "snap_point":(0, 0, 0), "snap_align":False, "snap_normal":(0, 0, 0), "gpencil_strokes":False, "cursor_transform":False, "texture_space":False, "remove_on_cancel":False, "release_confirm":False, "use_accurate":False, "use_automerge_and_split":False})
    # TEMPORARY!
            bpy.ops.mesh.extrude_region_move(MESH_OT_extrude_region={"use_normal_flip":False, "mirror":False}, 
                TRANSFORM_OT_translate={"value":(-0, -0, endDepth), "orient_type":'LOCAL', 
                "orient_matrix":((1, 0, 0), (0, 1, 0), (0, 0, 1)), "orient_matrix_type":'LOCAL', 
                "constraint_axis":(False, False, True), "mirror":False, "use_proportional_edit":False, 
                "proportional_edit_falloff":'SMOOTH', "proportional_size":0.620921, "use_proportional_connected":False, 
                "use_proportional_projected":False, "snap":False, "snap_target":'CLOSEST', "snap_point":(0, 0, 0), 
                "snap_align":False, "snap_normal":(0, 0, 0), "gpencil_strokes":False, "cursor_transform":False, 
                "texture_space":False, "remove_on_cancel":False, "release_confirm":False, "use_accurate":False})
            bpy.ops.object.editmode_toggle()

    #COVERAGE_CLASS Blender4CNC
    # class Blender4CNC main
    def __init__(self):
        self.debug = {}
        self.Parameters = Blender4CNC.Parameters()
        self.CreateOps = Blender4CNC.CreateOpsClass(self)
        self.EditOps = Blender4CNC.EditOpsClass(self)
        self.Errors = Blender4CNC.ErrorsClass(self)
        self.MogrifyOps = Blender4CNC.MogrifyOpsClass(self)
        self.MeshCleanup = Blender4CNC.MeshCleanupClass(self)
        #*************************************************************************
        # Will check that a project has all required objects that functions rely on
        # such as project parameters, colors, etc.
        #*************************************************************************
        #self.CheckProjectFundamentals()
        ks = bpy.data.objects.keys()
        if 'ProjectParameters' not in ks:
            raise Exception("Cannot find Project Parameters (needed for displaying error messages)?", (0,0))

        for s in ["Color4Blank", "Color4Parameters", "Color4Pockets", "Color4ResultBottom", "Color4ResultPaths", "Color4ResultSideWalls", "Color4ResultTop"]:
            if s not in ks:
                raise Exception("Cannot find object " + s + " (needed for displaying materials)?", (0,0))

        for s in ["GCodePreAmble", "GCodePostAmble", "MaterialBlank"]:
            if s not in ks:
                raise Exception("Cannot find object " + s + " (needed for GCode generation)?", (0,0))

        if "JobParameters" not in ks:
            raise Exception("Cannot find Job Parameters " + s + " (needed for GCode generation)?", (0,0))

        self.Parameters.SetProjectParameters()
        self.Parameters.CheckProjectParameters()

    #********************************************************************
    # 
    #********************************************************************
    def DEBUG_METHOD_HEADER(self, tf=False):
        if not tf:
            return (0,0,0)
        methodName = self.__class__.__name__ + "." + inspect.stack()[1][3]
        indent = None
        indent = " " * len(inspect.stack()) * 2
        self.debug[methodName] = tf
        if self.debug[methodName]:
            print(indent, methodName, "*" * 30)
        return (methodName, indent, self.debug[methodName])

    #*************************************************************************
    def GetTextObject(self, name):
        if name in bpy.data.objects.keys():
            ob = self.ReturnObjectByName(name)
            if ob.type == 'FONT':
                return ob.data.body.splitlines()
        return None

    # DUPLICATED IN VISUALPOLY !!!!!!!!!
    #*************************************************************************
    # Returns True if "name" starts with 3 digits and a period and then is 
    # followed by "s"
    #*************************************************************************
    def IsObjectNamed(self, name, s):
        return re.match("\d\d\d\." + s, name)

    # DUPLICATED IN VISUALPOLY AND PARAMETERS !!!!!!!!!
    #*************************************************************************
    # Find an object by name
    #*************************************************************************
    def ReturnObjectByName (self, passedName= ""):
        return bpy.data.objects[passedName]

    #*************************************************************************
    # Must be in OBJECT mode to call this function.
    # Toggle to EDIT MODE to unselect all vertices then toggle back to OBJECT
    # MODE.
    #*************************************************************************
    def EDIT_MODE_Deselect_All_OBJECT_MODE(self):
        bpy.ops.object.editmode_toggle()    # Enter Edit Mode
        bpy.ops.mesh.select_mode(type="VERT")
        bpy.ops.mesh.select_all(action = 'DESELECT')
        bpy.ops.object.editmode_toggle()    # Enter Object Mode

    #*************************************************************************
    # This function gets called when the user clicks the "Process Paths" 
    # button.
    #*************************************************************************
    def ProcessPaths(self, context) :
        try:
            startTime = datetime.datetime.now()
            # Create all the Python programs to produce the GCode
#            cProfile.runctx('listOfLists = self.ProcessCollections(context)', globals(), locals())
            proc = self.ProcessCollections(self)
            listOfLists = proc.ProcessCollections(context)
#            listOfLists = self.ProcessCollections(context)

#            cProfile.runctx('self.RunPythonProgramsAndVizualize(listOfLists)', globals(), locals())
            viz = self.VizualizeCollections(self, proc.listPrograms)
            viz.VizualizeCollections(listOfLists)
#            self.VizualizeCollections(listOfLists)
            # Print how long the process took
            endTime = datetime.datetime.now()
            d = endTime - startTime
            print("Total Elapsed time: ", d)
        except Exception as err:
            ob = self.Errors.FindOrCreateErrorMessage("ErrorText", err.args)
            raise err
        print("Finished.")            
        return {"FINISHED"}

    #*************************************************************************
    # This function gets called when the user clicks the "Just Produce GCode" 
    # button.
    #*************************************************************************
    def JustProduceGCode(self, context) :
        try:
            startTime = datetime.datetime.now()
            listOfLists = self.ProcessCollections(context)
            print("Total Elapsed time: ", datetime.datetime.now() - startTime)
        except Exception as err:
            ob = self.Errors.FindOrCreateErrorMessage("ErrorText", err.args)
            raise err
        print("Finished.")            
        return {"FINISHED"}

    def LoadGCodeFile(self, filename):
        inputFile = bpy.path.abspath(filename)
        objName = bpy.path.basename(filename)

        self.Parameters.SetProjectParameters()
        gcodePathViewer = self.GCodePathViewer()
        scale = 1
        gcodePathViewer.VisualizeGCodePath(objName, None, inputFile, False, self.Parameters.ProjectParameter("PathBevelDepth"), scale)



#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Mogrify 
# A class for when the user clicks "Create Path Left"
# A class for when the user clicks "Create Path Right"
# A class for when the user clicks "Expand Shape"
# A class for when the user clicks "Shrink Shape"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class CreateLeftPath(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_left_path", "", {"REGISTER", "UNDO"}, "Create Path to Left"
    def execute(self, context) :
        Blender4CNC().MogrifyOps.CreatePathLeft(context, context.scene.model2pyObject.distance, False) 
        return {"FINISHED"}

class CreateRightPath(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_right_path", "", {"REGISTER", "UNDO"}, "Create Path to Right"
    def execute(self, context) :
        Blender4CNC().MogrifyOps.CreatePathLeft(context, context.scene.model2pyObject.distance, True)        
        return {"FINISHED"}

class ExpandShape(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.expand_shape", "", {"REGISTER", "UNDO"}, "Expand Shape"
    def execute(self, context) :
        Blender4CNC().MogrifyOps.ExpandShape(context, context.scene.model2pyObject.distance, True)        
        return {"FINISHED"}

class ShrinkShape(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.shrink_shape", "", {"REGISTER", "UNDO"}, "Shrink Shape"
    def execute(self, context) :
        Blender4CNC().MogrifyOps.ExpandShape(context, context.scene.model2pyObject.distance, False)        
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class for when the user clicks "Create CW Pocket"
# A class for when the user clicks "Create Tenon"
# A class for when the user clicks "Create CCW Pocket"
# A class for when the user clicks "Create Closed Path"
# A class for when the user clicks "Create Open Path"
# A class for when the user clicks "Create Hole"
# A class for when the user clicks "Create Drill Path"
# A class for when the user clicks "Create Arc Path"
# A class for when the user clicks "Create Circle Path"
# A class for when the user clicks "Create Circle Pocket"
# A class for when the user clicks "Create DepthImage"
# A class for when the user clicks "Create Parameter"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class CreatePocket(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_pocket", "", {"REGISTER", "UNDO"}, "Create CW Pocket"
    def execute(self, context):
        Blender4CNC().CreateOps.CreateCWPocket()
        return {"FINISHED"}

class CreateTenon(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_tenon", "", {"REGISTER", "UNDO"}, "Create Tenon"
    def execute(self, context):
        Blender4CNC().CreateOps.CreateTenon()
        return {"FINISHED"}

class CreateCCWPocket(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_ccw_pocket", "", {"REGISTER", "UNDO"}, "Create CCW Pocket"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateCCWPocket()
        return {"FINISHED"}

class CreateClosedPath(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_closed_path", "", {"REGISTER", "UNDO"}, "Create Closed Path"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateClosedPath()
        return {"FINISHED"}

class CreateOpenPath(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_open_path", "", {"REGISTER", "UNDO"}, "Create Open Path"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateOpenPath()
        return {"FINISHED"}

class CreateHole(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_hole", "", {"REGISTER", "UNDO"}, "Create Hole"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateHole()
        return {"FINISHED"}

class CreateDrillPath(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_drill_path", "", {"REGISTER", "UNDO"}, "Create DrillPath"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateDrillPath()
        return {"FINISHED"}

class CreateArcPath(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_arc_path", "", {"REGISTER", "UNDO"}, "Create Arc Path"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateArcPath()
        return {"FINISHED"}

class CreateCirclePath(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_circle_path", "", {"REGISTER", "UNDO"}, "Create Circle Path"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateCirclePath()
        return {"FINISHED"}

class CreateCirclePocket(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_circle_pocket", "", {"REGISTER", "UNDO"}, "Create Circle Pocket"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateCirclePocket()
        return {"FINISHED"}

class CreateDepthImage(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_depthimage", "", {"REGISTER", "UNDO"}, "Create DepthImage"
    def execute(self, context):
        Blender4CNC().CreateOps.CreateDepthImage()
        return {"FINISHED"}

class CreateParameter(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_parameter", "", {"REGISTER", "UNDO"}, "Create Parameter"
    def execute(self, context) :
        Blender4CNC().CreateOps.CreateParameter()
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class for when the user clicks "Clean Meshes"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class CleanMesh(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.clean_mesh", "", {"REGISTER", "UNDO"}, "Clean Meshes"

    def execute(self, context) :
        Blender4CNC().MeshCleanup.CleanMeshes(context)        
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class for when the user clicks "CheckMeshes"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class CheckMesh(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.check_mesh", "", {"REGISTER", "UNDO"}, "Check Meshes"

    def execute(self, context) :
        Blender4CNC().MeshCleanup.CheckMeshes(context)        
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class for when the user clicks "Process Paths"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class ProcessPaths(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.process_paths", "Process Paths", {"REGISTER", "UNDO"}, "Process Paths"

    def execute(self, context) :
#        cProfile.runctx('Blender4CNC().ProcessPaths(context)', globals(), locals())
        Blender4CNC().ProcessPaths(context)        
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class for when the user clicks "Just Produce GCode"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class JustProduceGCode(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.just_produce_gcode", "Just Produce GCode", {"REGISTER", "UNDO"}, "Just Produce GCode"

    def execute(self, context) :
#        cProfile.runctx('Blender4CNC().ProcessPaths(context)', globals(), locals())
        Blender4CNC().JustProduceGCode(context)        
        return {"FINISHED"}


#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to display the GUI panel for Object mode - Process Paths, Clean Meshes, Create Paths and Pockets 
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class Model2Py2GCode_PT_Panel(bpy.types.Panel) :
    bl_idname = 'MODEL2PY2GCODE_PT_Panel'
    bl_label = 'GCode'
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'GCODE'

    bl_context = "objectmode"
    bl_label = "Blender4CNC"

    def draw(self, context) :
        m2pO = context.scene.model2pyObject
        TheCol = self.layout.column(align = True)
        TheCol.operator("mesh.process_paths", text = "Process Paths", icon="PLAY")
        TheCol.operator("mesh.just_produce_gcode", text = "Just Produce GCode", icon="PLAY")
        self.layout.label(text=" ")
        TheCol = self.layout.column(align = True)
        TheRow = self.layout.row(align = False)
        TheRow.operator("mesh.clean_mesh", text = " ", icon="TOOL_SETTINGS") # text = "Clean Meshes"
        TheRow.operator("mesh.check_mesh", text = " ", icon="ERROR") # text = "Check Meshes"
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        self.layout.label(text="")
        TheCol = self.layout.column(align = True)
        TheCol.prop(m2pO, "distance")
        TheRow = self.layout.row(align = False)
        TheRow.operator("mesh.create_right_path", text=" ", icon="TRACKING_FORWARDS_SINGLE") # text = "Create Path Right"
        TheRow.operator("mesh.create_left_path", text=" ", icon="TRACKING_BACKWARDS_SINGLE") # text = "Create Path Left"
        TheRow.operator("mesh.expand_shape", text=" ", icon="MOD_SKIN") # text = "Expand Shape"
        TheRow.operator("mesh.shrink_shape", text=" ", icon="MOD_MESHDEFORM") # text = "Shrink Shape"
#        TheRow.operator("mesh.expand_shape", text=" ", icon="MOD_SKIN") # text = "Expand Shape"
#        TheRow.operator("mesh.shrink_shape", text=" ", icon="MOD_MESHDEFORM") # text = "Shrink Shape"
#        TheRow.operator("mesh.expand_shape", text=" ", icon="FULLSCREEN_ENTER") # text = "Expand Shape"
#        TheRow.operator("mesh.shrink_shape", text=" ", icon="FULLSCREEN_EXIT") # text = "Shrink Shape"
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        self.layout.label(text=" ")
        TheCol = self.layout.column(align = True)
        TheRow = self.layout.row(align = False)
        TheRow.operator("mesh.create_pocket", text=" ", icon="SNAP_FACE")             # text = "CW Pocket"
        TheRow.operator("mesh.create_ccw_pocket", text=" ", icon="IMAGE_ALPHA")       # text = "CCW Pocket"
        TheRow.operator("mesh.create_closed_path", text=" ", icon="MESH_PLANE")       # text = "Closed Path"
        TheRow.operator("mesh.create_open_path", text=" ", icon="IPO_CONSTANT")          # text = "Open Path"
        TheRow.operator("mesh.create_hole", text=" ", icon="CLIPUV_DEHLT")            # text = "Hole"
        TheRow.operator("mesh.create_drill_path", text=" ", icon="LIGHTPROBE_GRID")   # text = "Drill Path"
        TheRow = self.layout.row(align = False)
        TheRow.operator("mesh.create_arc_path", text=" ", icon="SPHERECURVE")         # text = "Arc Path"
        TheRow.operator("mesh.create_circle_path", text=" ", icon="MESH_CIRCLE")         # text = "Circle Path"
        TheRow.operator("mesh.create_circle_pocket", text=" ", icon="SHADING_SOLID")         # text = "Circle Pocket"
        TheRow.operator("mesh.create_depthimage", text=" ", icon="IMAGE_DATA")         # text = "DepthImage"
        TheRow.operator("mesh.create_tenon", text=" ", text_ctxt="test", icon="IMAGE_ZDEPTH")       # text = ""
        TheRow.operator("mesh.create_parameter", text=" ", icon="OUTLINER_OB_FONT")         # text = ""

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to make a radius edge in edit mode
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class MakeRadius(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.make_radius", "", {"UNDO"}, "Make Radius Segment"

    def execute(self, context) :
        Blender4CNC().EditOps.MakeRadius()
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to unmake a radius edge in edit mode
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class UnMakeRadius(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.unmake_radius", "", {"UNDO"}, "Unmake Radius Segment"

    def execute(self, context) :
        Blender4CNC().EditOps.UnmakeRadius()
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to set the origin to the current selected vertex
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class SetOriginToVertex(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.set_origin_to_vertex", "", {"UNDO"}, "Set Origin to Selected Vertex"

    def execute(self, context):
        Blender4CNC().EditOps.SetOriginToVertex()
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A Class to mark the Start of a Curve
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class SetStartCurve(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.set_start_curve", "", {"UNDO"}, "Set Vertex as Start of Arc"

    def execute(self, context):
        Blender4CNC().EditOps.SetStartCurve(context)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A Class to mark the End of a Curve
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class SetEndCurve(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.set_end_curve", "", {"UNDO"}, "Set Vertex as End of Arc"

    def execute(self, context):
        Blender4CNC().EditOps.SetEndCurve(context)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to mark the center of a curve
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class SetCenterCurve(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.set_center_curve", "", {"UNDO"}, "Set Vertex as Center of Arc"

    def execute(self, context):
        Blender4CNC().EditOps.SetCenterCurve(context)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to create a CW curve (edit mode)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class CreateShortCurve3Points(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_short_curve", "", {"UNDO"}, "Create CW Curve"

    def execute(self, context):
        Blender4CNC().EditOps.CreateShortCurve3Points(context)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to create a CCW curve (edit mode)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class CreateCCWCurve3Points(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.create_ccw_curve", "", {"UNDO"}, "Create CCW Curve"

    def execute(self, context):
        Blender4CNC().EditOps.CreateCCWCurve3Points(context)        
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to create a curve edge (edit mode - start or end of curve)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class MakeCurve(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.make_curve", "", {"UNDO"}, "Make Curve Segment"

    def execute(self, context) :
        Blender4CNC().EditOps.MakeCurve()
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to unmake a curve edge (edit mode - start or end of curve)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class UnMakeCurve(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.unmake_curve", "", {"UNDO"}, "Unmake Curve Segment"

    def execute(self, context) :
        Blender4CNC().EditOps.UnmakeCurve()
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to remove curves (merge them down to just their start point)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class RemoveCurves(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.remove_curves", "", {"UNDO"}, "Reduce Curves to a single point."

    def execute(self, context) :
        Blender4CNC().EditOps.RemoveCurves(context)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to add a point at a distance and angle in edit mode
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class AddAPoint(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.add_a_point", "", {"UNDO"}, "Add a Point"

    def execute(self, context):
        Blender4CNC().EditOps.AddAPoint(context)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to make a start point in edit mode
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class MakeStartPoint(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.make_start_point", "", {"UNDO"}, "Make a Start Point"

    def execute(self, context):
        Blender4CNC().EditOps.MakeStartPoint(1)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to make an up point in edit mode
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class MakeUpPoint(bpy.types.Operator) :
    bl_idname, bl_label, bl_options, bl_description = "mesh.make_up_point", "", {"UNDO"}, "Make an Up Point"

    def execute(self, context):
        Blender4CNC().EditOps.MakeStartPoint(0.9)
        return {"FINISHED"}

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class to display the GUI panel for Edit Mode - Add a point at angle, distance, Make Start Point, 
# Make/Undo Curve, Make/Undo Radius
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class Model2Py2GCodeEdit_PT_Panel(bpy.types.Panel) :
    bl_idname = 'MODEL2PY2GCODEEDIT_PT_Panel'
    bl_label = 'GCode'
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'GCODE'

    bl_context = "mesh_edit"
    bl_label = "Model2Py2GCodeEdit"

    def draw(self, context) :
        m2p = context.scene.model2py
        m2p3Point = context.scene.model2py3Point
        TheCol = self.layout.column(align = True)
        TheRow = self.layout.row(align = True)
        TheRow.label(text="", icon = "DRIVER_ROTATIONAL_DIFFERENCE")
        TheRow.prop(m2p, "angle")
        TheRow = self.layout.row(align = True)
        TheRow.label(text="", icon = "DRIVER_DISTANCE")
        TheRow.prop(m2p, "distance")
        TheCol = self.layout.column(align = True)
        TheCol.operator("mesh.add_a_point", icon = "ADD") # text = "Add Point"
        self.layout.label(text=" ")
        TheRow = self.layout.row(align = False)
        TheRow.operator("mesh.make_start_point", text = " ", icon = "TRACKING_REFINE_FORWARDS") # text = "Make Start Point"
        TheRow.operator("mesh.make_radius", text = " ", icon = "GIZMO") # text = "Make Radius"
        TheRow.operator("mesh.unmake_radius", text = " ", icon = "PANEL_CLOSE") # text = "UnMake Radius"
        TheRow.operator("mesh.make_curve", text = " ", icon = "IPO_CIRC") # text = "Make Curve"
        TheRow.operator("mesh.unmake_curve", text = " ", icon = "IPO_LINEAR") # text = "UnMake Curve"
        TheRow.operator("mesh.set_origin_to_vertex", text = " ", icon = "EMPTY_AXIS") # text = "Set Origin To Vertex"
        TheRow = self.layout.row(align = False)
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.operator("mesh.remove_curves", text = " ", icon = "HANDLE_AUTO") # text = "Reduce curves to a single point"
        TheRow.operator("mesh.make_up_point", text = " ", icon = "EMPTY_SINGLE_ARROW") # text = "Make Up Point"
        self.layout.label(text=" ")
        TheRow = self.layout.row(align = True)
        TheRow.operator("mesh.set_start_curve", text = " ", icon = "FRAME_NEXT") # 
        TheRow.prop(m2p3Point, "startX", text = "")
        TheRow.prop(m2p3Point, "startY", text = "")
        TheRow = self.layout.row(align = True)
        TheRow.operator("mesh.set_end_curve", text = " ", icon = "FF") # 
        TheRow.prop(m2p3Point, "endX", text = "")
        TheRow.prop(m2p3Point, "endY", text = "")
        TheRow = self.layout.row(align = True)
        TheRow.operator("mesh.set_center_curve", text = " ", icon = "SNAP_MIDPOINT") # 
        TheRow.prop(m2p3Point, "centerX", text = "")
        TheRow.prop(m2p3Point, "centerY", text = "")
        TheRow = self.layout.row(align = False)
        TheRow.operator("mesh.create_short_curve", text = " ", icon = "TIME") # text = ""
        TheRow.operator("mesh.create_ccw_curve", text = " ", icon = "RECOVER_LAST") # text = ""
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.label(text=" ")
        TheRow.label(text=" ")

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Class containing properties to be displayed as GUI when in Edit mode for adding a point at angle and dist.
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class Model2PySettings(PropertyGroup):
    angle: FloatProperty(name="Angle", description = "", default=0, min=0, max=360, step=1, precision=3)
    distance: FloatProperty(name="Distance", description = "", default=0, min=0, max=1000, step=1, precision=3)

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Class containing properties to be displayed as GUI when in Edit mode for creating a curve from 3 points
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class Model2PySettings3Point(PropertyGroup):
    startX: FloatProperty(name="StartX", description = "", default=0, step=1, precision=3)
    startY: FloatProperty(name="StartY", description = "", default=0, step=1, precision=3)
    endX: FloatProperty(name="EndX", description = "", default=0, step=1, precision=3)
    endY: FloatProperty(name="EndY", description = "", default=0, step=1, precision=3)
    centerX: FloatProperty(name="CenterX", description = "", default=0, step=1, precision=3)
    centerY: FloatProperty(name="CenterY", description = "", default=0, step=1, precision=3)

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Class containing properties to be displayed as GUI when in object mode for the Functions: 
# "Create Path Right", "Create Path Left", "Expand Shape", and "Shrink Shape"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class Model2PySettingsObjectMode(PropertyGroup):
    distance: FloatProperty(name="Path Distance:", description = "Path Distance", default=0.25, min=0, max=1000, step=0.05, precision=3)

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class for calling out to ImageMagick (MagickStr is only used during testing)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class ImageMagick:

    #**************************************************************************
    # Convert a command line string into a list suitable for subprocess
    #**************************************************************************
    def MagickStr(self, s):
        subprocess.call(["magick"] + shlex.split(s))

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class for creating the GUI panel for a depth panel (not used)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class Im2GCodeOp(bpy.types.Operator) :
    bl_idname = "mesh.process_image"
    bl_label = "Process Image"
    bl_options = {"REGISTER", "UNDO"}

    def __init__(self):
        pass

    #*************************************************************************
    # This function gets called when the user clicks the "Process Image" 
    # button.
    #*************************************************************************
    def execute(self, context) :

        # Get the GUI parameters
        i2g = context.scene.im2gcode
        self.i2g = context.scene.im2gcode
        
        # Check the parameters make sense
        print("Checking Parameters")
        if not os.path.isfile(i2g.file_name):
            self.report({'ERROR'}, "Cannot find image file: %s." % i2g.file_name)
            return {"CANCELLED"}
        if (i2g.final_dia >= i2g.rough_dia):
            self.report({'ERROR'}, "Final bit diameter must be <= rough bit diameter.")
            return {"CANCELLED"}
        if (i2g.carve_dia >= i2g.final_dia):
            self.report({'ERROR'}, "Carve bit diameter must be <= final bit diameter.")
            return {"CANCELLED"}
        if (i2g.zstep <= i2g.max_depth):
            self.report({'ERROR'}, "ZStep must be smaller than Max Depth.")
            return {"CANCELLED"}

        # The y step must be an integer fraction of the final diameter
        mult = i2g.final_dia / i2g.ystep;
        mult = mult % 1
        if (mult > 0.0001):
            self.report({'ERROR'}, "YStep must be integer fraction of final bit diameter (sorry).")
            return {"CANCELLED"}

        # If doing a lamination, the total layers must exceed the max depth
        # and the max depth must fall within the last layer
        if i2g.number_layers > 1:
            total = i2g.laminate_thickness * i2g.number_layers
            if total < (-i2g.max_depth):
                self.report({'ERROR'}, "Max Depth exceeds total laminate thickness.")
                return {"CANCELLED"}
            total = -i2g.laminate_thickness * (i2g.number_layers-1)
            if total < (i2g.max_depth):
                self.report({'ERROR'}, "Max Depth does not cut all laminate layers.")
                return {"CANCELLED"}
        
        image2GCode = Im2GCode()
        image2GCode.Go_Image2GCode()
        return {"FINISHED"}
 
##++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
##++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## Structure class to hold current position and entrance direction when tracing blobs in images
##++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
##++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#class Blender4CNC.MyPix:

#    def __init__(self, x2, y2, dx2, dy2):
#        self.x = int(x2)
#        self.y = int(y2)
#        self.dx = int(dx2)
#        self.dy = int(dy2)

#    def __repr__(self):
#        return "(" + str(self.x) + ", " + str(self.y) + ", " + str(self.dx) + ", " + str(self.dy) + ")"

#    def IsLocationEqual(self, p):
#        return ((self.x == p.x) and (self.y == p.y))

#    def IsDirectionEqual(self, p):
#        return ((self.dx == p.dx) and (self.dy == p.dy))

#    def ToString(self):
#     return "%d,%d,%d,%d" % (self.x,self.y,self.dx,self.dy)

#    def InsideArea(self, xMin, xMax, yMin, yMax):
#        return ((self.x >= xMin) and (self.x <= xMax) and (self.y >= yMin) and (self.y <= yMax))

#    def MoveInDirection(self):
#        self.x += int(self.dx)
#        self.y += int(self.dy)

#    def Rotate180(self):
#        self.dy = int(-self.dy)
#        self.dx = int(-self.dx)

#    # Rotating cw by 90 Matrix
#    #  0, 1
#    # -1, 0
#    # New x = old y, New y = -old x
#    def Rotate90CW(self):
#        t = int(self.dy)
#        self.dy = int(-self.dx)
#        self.dx = int(t)

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# A class that can parse a GCode file and create a curve object representing the tool path
# Called when the user presses the "Load G Code" button on the UI interface.
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class LoadGCodeOp(bpy.types.Operator) :
    bl_idname = "mesh.load_gcode"
    bl_label = "Load GCode"
    bl_options = {"REGISTER", "UNDO"}

    def __init__(self):
        pass

    #*************************************************************************
    # This function gets called when the user clicks the "Load GCode" 
    # button.
    #*************************************************************************
    def execute(self, context) :
        lg = context.scene.loadgcode
        Blender4CNC().LoadGCodeFile(lg.file_name)        
        return {"FINISHED"}
 
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Class to display the Load GCode UI Panel
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class LoadGCode_PT_Panel(bpy.types.Panel):
    bl_idname = 'LOADGCODE_PT_Panel'
    bl_label = 'GCode'
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = 'GCODE'
    bl_context = "objectmode"
    bl_label = "LoadGCode"

    def draw(self, context):
        lg = context.scene.loadgcode
        TheCol = self.layout.column(align = True)
        row = TheCol.row(align=True)
        row.prop(lg, 'file_name', text="")
        TheCol.operator("mesh.load_gcode", text = "Load GCode")

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Class containing properties to be displayed as GUI to user for "Load G Code"
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class LoadGCodeSettings(PropertyGroup):
    file_name: StringProperty(name = "File Name", description = "GCode file", subtype="FILE_PATH")

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Preferences for the Blender4CNC Addon (Not Used)
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
class LoadGCodePreferences(bpy.types.AddonPreferences):
    bl_idname = __name__
 
    rs274Path: StringProperty(name = "RS274 Path", description = "Path to rs274 executable", subtype="FILE_PATH")
 
    def draw(self, context):
        layout = self.layout
        row = layout.row()
        row.prop(self, 'rs274Path', expand=True)
 
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
# Registering the Blender4CNC Addon
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
classes = (
    # Panels - 2 for object mode, 1 for edit mode
    LoadGCode_PT_Panel,
    Model2Py2GCode_PT_Panel,
    Model2Py2GCodeEdit_PT_Panel,

    # Preferences for the Addon (not used)
    LoadGCodePreferences,

    # The property that holds the GCode file string to load
    LoadGCodeSettings,
    # The class that can load a GCode file
    LoadGCodeOp,

    # Properties for the Blender4CNC functions
    Model2PySettings,
    Model2PySettings3Point,
    Model2PySettingsObjectMode,
    
    # Object mode buttons
    CleanMesh, CheckMesh,
    CreateRightPath, CreateLeftPath, ExpandShape, ShrinkShape,
    CreatePocket, CreateCCWPocket, CreateClosedPath, CreateOpenPath, CreateHole, CreateDrillPath, 
    CreateArcPath, CreateCirclePath, CreateCirclePocket, CreateDepthImage, CreateTenon, CreateParameter,
    ProcessPaths,
    JustProduceGCode,

    # Edit mode buttons
    AddAPoint, MakeStartPoint, MakeRadius, UnMakeRadius, MakeCurve, UnMakeCurve, SetOriginToVertex, 
    RemoveCurves, MakeUpPoint,
    CreateShortCurve3Points, SetStartCurve, SetEndCurve, SetCenterCurve, CreateCCWCurve3Points, 

    Im2GCodeOp,
)

def register():
    from bpy.utils import register_class
    for cls in classes:
        register_class(cls)
    bpy.types.Scene.loadgcode = PointerProperty(type=LoadGCodeSettings)
    bpy.types.Scene.model2py = PointerProperty(type=Model2PySettings)
    bpy.types.Scene.model2py3Point = PointerProperty(type=Model2PySettings3Point)
    bpy.types.Scene.model2pyObject = PointerProperty(type=Model2PySettingsObjectMode)

def unregister():
    from bpy.utils import unregister_class
    for cls in reversed(classes):
        unregister_class(cls)
    del bpy.types.Scene.loadgcode
    del bpy.types.Scene.model2py
    del bpy.types.Scene.model2py3Point
    del bpy.types.Scene.model2pyObject
    del bpy.types.Scene.im2gcode

if __name__ == '__main__':
    register()

