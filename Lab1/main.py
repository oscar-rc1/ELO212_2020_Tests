#!/usr/bin/env python3

import pygame
import sys
import math
import os
import platform
import pyverilator

from time import time
from random import choice,randint

# Variables y constantes globales

constFPS = 144
constWidth = 64 * 9
constHeight = 100

pygame.init()
pygame.display.set_caption("TestVerilator")

gScreen = pygame.display.set_mode((constWidth, constHeight))
gSurface = pygame.Surface((constWidth, constHeight))
gClock = pygame.time.Clock()

# Elementos

from seven_seg import *

# Ejecutar simulación

sim = pyverilator.PyVerilator.build("dut/parte3_main.sv", ["dut/"])

sim.io.rst = 1
sim.io.clk = 0
sim.io.clk = 1
sim.io.rst = 0

gTime = 0
gData = []

while gTime != 100000:
	sim.io.clk = 0
	sim.io.clk = 1

	if not len(gData) or (sim.io.sseg, sim.io.an) != gData[-1]:
		gData.append( (gTime/10000, sim.io.sseg, sim.io.an) )

	if gTime % 10000 == 0 and gTime != 0:
		print("Simulación: {0}%".format(round(gTime / 1000),1))

	gTime += 1

# Dibujar simulación

gTime = 0
gDataIdx = 0
gExecLoop = 1
gFrame = 0

def next_index(time, current_idx):
	for i in range(current_idx + 1, len(gData)):
		if gData[i][0] >= time:
			return i

	return 0

while gExecLoop:
	gFrame += 1

	if gFrame == constFPS:
		gFrame = 0

	gClock.tick(constFPS)

	gSurface.fill((255, 255, 255))

	_, sseg, an = gData[gDataIdx]

	for i in range(8):
		draw_sseg(gSurface, gTime, i, sseg, 1, an & (1 << i), 480 - 70*i, 8)

	gTime += 1 / constFPS;
	gDataIdx = next_index(gTime, gDataIdx)

	for event in pygame.event.get():
		if event.type == pygame.QUIT:
			gExecLoop = 0
			break

	gScreen.blit(gSurface, (0, 0))
	pygame.display.flip()

pygame.quit()
