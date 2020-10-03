
import pygame

gSegmentLog = [(0, 0, 0)] * 8
gSegmentSprites = {k: pygame.image.load("img/sseg_on_" + k + ".png").convert_alpha() for k in "abcdefgh"}

def draw_sseg(surface, time, idx, segments, dot, an, x, y):
	global gSegmentLog

	if not an:
		gSegmentLog[idx] = (time, segments, dot)
	elif time - gSegmentLog[idx][0] <= 0.1:
		_, segments, dot = gSegmentLog[idx]
	else:
		segments = 0x7F
		dot = 1

	for k in "abcdefg":
		if not segments % 2:
			surface.blit(gSegmentSprites[k], (x, y))

		segments //= 2

	if not dot:
		surface.blit(gSegmentSprites["h"], (x, y))
