import io
import os
import re
import time
import random
from datetime import datetime
from collections import deque

import gspread
from gspread.exceptions import APIError
from oauth2client.service_account import ServiceAccountCredentials
from googleapiclient.discovery import build

from PIL import Image, ImageDraw, ImageFont, ImageFilter, ImageOps  # add ImageOps

import json
import requests

import argparse
from urllib.parse import quote

import torch
from torchvision import transforms
from transformers import AutoModelForImageSegmentation

from PIL import Image, ImageDraw, ImageFont, ImageFilter

try:
    from pillow_heif import register_heif_opener
    register_heif_opener()
except Exception:
    pass


# ============================================================
# CONFIG
# ============================================================
CREDENTIALS_FILE = 'credentials.json'

LINEUPS_SHEET_ID = '1T_Sc_t6n5E_tKpnDEjzd4-6th1T-kHexK-bGezxnZ30'
INDEX_SHEET_ID = '1j6ZN3N8aXnB9vKFdWeXhY-fyo8aH1JlmhWZWHwzgu-E'

ASSETS_FOLDER_ID = '1-MAJwpIAjQvzXQdsPdqmkX4NGrM8YFt5'
LOGO_FOLDER_ID = '19NNyf1trl1LoA7Tth7PFMbRAv65oXeeR'
PLAYERS_ROOT_FOLDER_ID = '1ul10SG2lD5vOjwR0hpQPPb6FqLWFcc3N'

POST_TO_META_ONLINE = True

OUTPUT_DIR = 'output'
FONT_FILE = 'Anton-Regular.ttf'

OUR_TEAMS = ('11A', '11B', '11C')

MD_BACKGROUND_NAME_FOR_TEAM = {
    '11A': '11A Match Day',
    '11B': '11B Match Day',
    '11C': '11C Match Day',
}

FIXTURES_FRIENDLY_TAB = 'Friendly Fixtures'
FIXTURES_LEAGUECUP_TAB = 'League & Cup Fixtures'

# Lineups columns, zero-based
COL_MATCH_DATE = 1
COL_STARTERS = 2
COL_SUBS = 3
COL_STATUS = 7
COL_MD_PICTURE = 9

# Fixtures columns, zero-based
FIX_COL_DATE = 0
FIX_COL_TIME = 1
FIX_COL_HOME = 2
FIX_COL_AWAY = 3
FIX_COL_LOCATION = 4
FIX_COL_MTYPE = 5
FIX_COL_ROUND = 6

RECENT_ROWS = 6

WHITE = (255, 255, 255)

MD_W = 768
MD_H = 960

RIGHT_BLOCK_LEFT = int(MD_W * 0.50)
RIGHT_BLOCK_RIGHT = MD_W - 18
RIGHT_BLOCK_MAX_W = RIGHT_BLOCK_RIGHT - RIGHT_BLOCK_LEFT
TEXT_CX = int((RIGHT_BLOCK_LEFT + RIGHT_BLOCK_RIGHT) / 2)

TEAM_BLOCK_CY = int(MD_H * 0.550)

VERT_GAP = int(MD_H * 0.145)

LOGOS_Y = TEAM_BLOCK_CY + VERT_GAP
INFO_Y = LOGOS_Y + int(MD_H * 0.125)

TEAM_LINE_GAP = 8
TEAM_TEXT_MAX_W = RIGHT_BLOCK_MAX_W
INFO_TEXT_MAX_W = RIGHT_BLOCK_MAX_W

TEAM_SIZE = 42
INFO_SIZE = 29

LOGO_MAX = 150
HOME_LOGO_CX = int(MD_W * 0.58)
AWAY_LOGO_CX = int(MD_W * 0.86)

PHOTO_LEFT = -35
PHOTO_RIGHT = int(MD_W * 0.55)
PHOTO_TOP = int(MD_H * 0.245)
PHOTO_BOTTOM = MD_H + 20

IMG_EXT = ('.png', '.jpg', '.jpeg', '.webp', '.heic', '.heif')


# ============================================================
# AUTH / API
# ============================================================
def get_creds():
    scope = [
        'https://spreadsheets.google.com/feeds',
        'https://www.googleapis.com/auth/drive'
    ]
    return ServiceAccountCredentials.from_json_keyfile_name(CREDENTIALS_FILE, scope)


def get_gspread_client():
    return gspread.authorize(get_creds())


def get_drive_service():
    return build('drive', 'v3', credentials=get_creds())


def with_retry(func, *args, retries=6, base_delay=3, **kwargs):
    for attempt in range(retries):
        try:
            return func(*args, **kwargs)
        except APIError as e:
            code = getattr(getattr(e, 'response', None), 'status_code', None)
            if code not in (429, 500, 502, 503, None) or attempt == retries - 1:
                raise
            time.sleep(base_delay * (2 ** attempt) + random.random())


# ============================================================
# HELPERS
# ============================================================
REPO_RAW_BASE = 'https://raw.githubusercontent.com/expediansunited-coder/galaksia-match-day/main'


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument('--generate-only', action='store_true')
    p.add_argument('--post-only', action='store_true')
    return p.parse_args()

def github_raw_url(path):
    p = path.replace('\\', '/')
    return f'{REPO_RAW_BASE}/{quote(p)}'

def safe_filename(s):
    s = str(s or '').strip()
    return re.sub(r'[^A-Za-z0-9]+', '_', s).strip('_') or 'file'

def _norm(s):
    if not s:
        return ''
    import unicodedata
    s = unicodedata.normalize('NFKD', s)
    s = ''.join(c for c in s if not unicodedata.combining(c))
    s = s.lower()
    return re.sub(r'[^a-z0-9]+', '', s)


def _tokens(s):
    if not s:
        return []
    import unicodedata
    s = unicodedata.normalize('NFKD', s)
    s = ''.join(c for c in s if not unicodedata.combining(c)).lower()
    return [t for t in re.split(r'[^a-z0-9]+', s) if t]


def parse_date(value):
    s = (value or '').strip()
    for fmt in ('%m/%d/%Y', '%m/%d/%y'):
        try:
            return datetime.strptime(s, fmt).date()
        except ValueError:
            pass
    return None


def split_names(cell):
    return [x.strip() for x in (cell or '').split(',') if x.strip()]


def load_font(size):
    path = os.path.join(os.path.dirname(__file__), FONT_FILE)
    return ImageFont.truetype(path, size)


def clean_team_name(name):
    s = (name or '').strip()

    s = re.sub(r'["“”„‟]+([A-ZÁ-Ž])["“”„‟]+', r'\1', s)
    s = re.sub(r'\b(z\s*\.?\s*s|s\s*\.?\s*r\s*\.?\s*o|a\s*\.?\s*s|o\s*\.?\s*s)\.?\b', '', s, flags=re.I)

    s = re.sub(r'\s+', ' ', s)
    s = re.sub(r'\s*,\s*$', '', s)

    return s.strip()


def our_display(team):
    t = team.upper().strip()
    if t in ('11A', '11B', '11C'):
        return 'GP23' + t[-1]
    return 'GP23'


def display_team_for_line(name):
    n = (name or '').strip()
    if _norm(n) in ('11a', '11b', '11c') or 'galaksia' in n.lower():
        return our_display(n)
    return n.upper()


def split_team_name_if_needed(name):
    """
    TJ SOKOL PÍSNICE B -> TJ SOKOL B / PÍSNICE
    Only for wrapping long team names.
    """
    toks = clean_team_name(name).upper().split()

    if len(toks) >= 4 and toks[-1] in ('A', 'B', 'C', 'D'):
        first_line = toks[:-2] + [toks[-1]]
        second_line = toks[-2]
        return ' '.join(first_line), second_line

    if len(toks) >= 4 and toks[-2] in ('A', 'B', 'C', 'D'):
        first_line = toks[:-1]
        second_line = toks[-1]
        return ' '.join(first_line), second_line

    return ' '.join(toks), ''

def is_our_team_name(name):
    n = (name or '').strip()
    return _norm(n) in ('11a', '11b', '11c') or 'galaksia' in n.lower()


def text_width(draw, text, font):
    b = draw.textbbox((0, 0), text, font=font)
    return b[2] - b[0]


def text_height(draw, text, font):
    b = draw.textbbox((0, 0), text, font=font)
    return b[3] - b[1]


def ellipsize_to_width(draw, text, font, max_w):
    text = str(text or '')
    if text_width(draw, text, font) <= max_w:
        return text

    ell = '…'
    while text and text_width(draw, text + ell, font) > max_w:
        text = text[:-1].rstrip()

    return text + ell if text else ell


def draw_centered_segments(draw, segments, cy):
    total_w = sum(text_width(draw, txt, font) for txt, font, fill in segments)
    max_h = max(text_height(draw, txt, font) for txt, font, fill in segments)

    x = TEXT_CX - total_w / 2

    for txt, font, fill in segments:
        b = draw.textbbox((0, 0), txt, font=font)
        y = cy - max_h / 2 - b[1]
        draw.text((int(x - b[0]), int(y)), txt, font=font, fill=fill)
        x += b[2] - b[0]

def draw_axis_centered_segments(draw, left_text, left_font, sep_text, sep_font, right_text, right_font, cy, gap=12):
    """
    Draws:
        left_text   sep_text   right_text

    with sep_text centered exactly on TEXT_CX.
    """
    max_h = max(
        text_height(draw, left_text, left_font),
        text_height(draw, sep_text, sep_font),
        text_height(draw, right_text, right_font)
    )

    sep_w = text_width(draw, sep_text, sep_font)
    sep_x = TEXT_CX - sep_w / 2

    left_w = text_width(draw, left_text, left_font)
    left_x = sep_x - gap - left_w

    right_x = sep_x + sep_w + gap

    for txt, font, x in (
        (left_text, left_font, left_x),
        (sep_text, sep_font, sep_x),
        (right_text, right_font, right_x),
    ):
        b = draw.textbbox((0, 0), txt, font=font)
        h = b[3] - b[1]
        y = cy - max_h / 2 - b[1]
        draw.text((int(x - b[0]), int(y)), txt, font=font, fill=WHITE)

def fit_text_font(draw, text, start_size, max_w, min_size=18):
    size = start_size

    while size > min_size:
        font = load_font(size)
        if text_width(draw, text, font) <= max_w:
            return font, text
        size -= 1

    font = load_font(min_size)
    return font, ellipsize_to_width(draw, text, font, max_w)

# ============================================================
# DRIVE
# ============================================================
def download_file_bytes(drive, file_id):
    return drive.files().get_media(fileId=file_id).execute()


def list_folder_files(drive, folder_id):
    out = []
    token = None
    while True:
        resp = drive.files().list(
            q=f"'{folder_id}' in parents and trashed = false",
            fields='nextPageToken, files(id,name,mimeType)',
            pageToken=token
        ).execute()
        out.extend(resp.get('files', []))
        token = resp.get('nextPageToken')
        if not token:
            break
    return out


def download_image_by_name(drive, name, folder_id=ASSETS_FOLDER_ID):
    target = os.path.splitext(name)[0].strip().lower()
    for f in list_folder_files(drive, folder_id):
        base = os.path.splitext(f['name'])[0].strip().lower()
        if base == target:
            data = download_file_bytes(drive, f['id'])
            return Image.open(io.BytesIO(data)).convert('RGBA')
    return None


def find_logo_file(files, name):
    target = _norm(os.path.splitext(name)[0])
    for f in files:
        if _norm(os.path.splitext(f['name'])[0]) == target:
            return f

    tset = set(_tokens(name))
    best = None
    for f in files:
        lset = set(_tokens(os.path.splitext(f['name'])[0]))
        if tset and (tset <= lset or lset <= tset):
            return f
        if tset & lset:
            best = f
    return best


def list_subfolders(drive, parent_id):
    out = []
    token = None
    while True:
        resp = drive.files().list(
            q=f"'{parent_id}' in parents and mimeType = 'application/vnd.google-apps.folder' and trashed = false",
            fields='nextPageToken, files(id,name)',
            pageToken=token
        ).execute()
        out.extend(resp.get('files', []))
        token = resp.get('nextPageToken')
        if not token:
            break
    return out


def list_images_in_folder(drive, folder_id):
    return [
        f for f in list_folder_files(drive, folder_id)
        if f['name'].lower().endswith(IMG_EXT) or f.get('mimeType', '').startswith('image/')
    ]


# ============================================================
# IMAGE PROCESSING
# ============================================================
def remove_edge_background(img, tol=60):
    img = img.convert('RGBA')
    w, h = img.size
    px = img.load()

    corners = [px[0, 0], px[w - 1, 0], px[0, h - 1], px[w - 1, h - 1]]
    bg = tuple(sum(c[i] for c in corners) // 4 for i in range(3))

    mask = bytearray(w * h)
    for y in range(h):
        for x in range(w):
            c = px[x, y]
            dist = abs(c[0] - bg[0]) + abs(c[1] - bg[1]) + abs(c[2] - bg[2])
            mask[y * w + x] = 0 if dist < tol else 1

    q = deque()
    seen = bytearray(w * h)

    for x in range(w):
        for y in (0, h - 1):
            idx = y * w + x
            if mask[idx] == 0:
                q.append((x, y))
                seen[idx] = 1

    for y in range(h):
        for x in (0, w - 1):
            idx = y * w + x
            if mask[idx] == 0:
                q.append((x, y))
                seen[idx] = 1

    while q:
        x, y = q.popleft()
        px[x, y] = px[x, y][:3] + (0,)
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            nx, ny = x + dx, y + dy
            if 0 <= nx < w and 0 <= ny < h:
                idx = ny * w + nx
                if not seen[idx] and mask[idx] == 0:
                    seen[idx] = 1
                    q.append((nx, ny))

    cb = img.getbbox()
    return img.crop(cb) if cb else img


def crop_to_content(img):
    cb = img.getbbox()
    return img.crop(cb) if cb else img


def add_white_glow(img, radius=6, expand=20):
    base = Image.new('RGBA', (img.width + expand * 2, img.height + expand * 2), (0, 0, 0, 0))
    base.alpha_composite(img, (expand, expand))

    alpha = base.split()[3]
    white = Image.new('RGBA', base.size, (255, 255, 255, 0))
    white.putalpha(alpha)

    glow = white.filter(ImageFilter.GaussianBlur(radius))
    out = Image.alpha_composite(glow, base)

    out.info['content_bbox'] = (
        expand,
        expand,
        expand + img.width,
        expand + img.height
    )
    return out


# ============================================================
# PLAYER PHOTO
# ============================================================
_PLAYER_FOLDERS = None


def get_player_folders(drive):
    global _PLAYER_FOLDERS

    if _PLAYER_FOLDERS is not None:
        return _PLAYER_FOLDERS

    top = list_subfolders(drive, PLAYERS_ROOT_FOLDER_ID)

    indiv = None
    for f in top:
        if _norm(f['name']) == _norm('Individual Photos'):
            indiv = f['id']
            break

    _PLAYER_FOLDERS = list_subfolders(drive, indiv) if indiv else top
    return _PLAYER_FOLDERS


def find_player_folder_id(drive, player_name):
    target = _norm(player_name)

    def base(folder_name):
        return _norm(re.sub(r'\s*\([^)]*\)\s*$', '', folder_name))

    folders = get_player_folders(drive)

    for f in folders:
        if base(f['name']) == target:
            return f['id']

    for f in folders:
        b = base(f['name'])
        if target in b or b in target:
            return f['id']

    return None

# ============================================================
# BIREFNET BACKGROUND REMOVAL
# ============================================================
BIR_DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
_BIR_MODEL = None

_BIR_TRANSFORM = transforms.Compose([
    transforms.Resize((1024, 1024)),
    transforms.ToTensor(),
    transforms.Normalize(
        [0.485, 0.456, 0.406],
        [0.229, 0.224, 0.225]
    )
])


def get_birefnet_model():
    global _BIR_MODEL

    if _BIR_MODEL is None:
        print(f'Loading BiRefNet on {BIR_DEVICE}...')

        _BIR_MODEL = AutoModelForImageSegmentation.from_pretrained(
            "ZhengPeng7/BiRefNet",
            trust_remote_code=True
        )

        _BIR_MODEL = _BIR_MODEL.to(BIR_DEVICE)
        _BIR_MODEL = _BIR_MODEL.float()
        _BIR_MODEL.eval()

        print('BiRefNet dtype:', next(_BIR_MODEL.parameters()).dtype)

    return _BIR_MODEL


def remove_bg_birefnet(data):
    image = Image.open(io.BytesIO(data))
    image = ImageOps.exif_transpose(image)
    image = image.convert("RGB")
    original_size = image.size

    model = get_birefnet_model()
    input_tensor = _BIR_TRANSFORM(image).unsqueeze(0)
    input_tensor = input_tensor.to(device=BIR_DEVICE, dtype=torch.float32)

    with torch.no_grad():
        pred = model(input_tensor)[-1].sigmoid().detach().cpu()[0].squeeze()

    pred = pred.float()

    mask = transforms.ToPILImage()(pred)
    mask = mask.resize(original_size, Image.LANCZOS)

    out = image.convert("RGBA")
    out.putalpha(mask)

    return out

def get_player_photo(drive, player_name):
    folder_id = find_player_folder_id(drive, player_name)
    if not folder_id:
        print(f'  [photo] no folder: {player_name}')
        return None

    imgs = [
        f for f in list_images_in_folder(drive, folder_id)
        if os.path.splitext(f['name'])[0].strip().lower() == 'left'
    ]

    random.shuffle(imgs)

    for f in imgs:
        try:
            data = download_file_bytes(drive, f['id'])
            img = remove_bg_birefnet(data)
            img = crop_to_content(img)
            img = add_white_glow(img)
            print(f'  [photo] {player_name}: {f["name"]}')
            return img
        except Exception as e:
            print(f'  [photo] skip {player_name}: {e}')

    return None


def pick_player_with_photo(drive, players, recent_names):
    recent_norm = [_norm(x) for x in recent_names if x]

    preferred = [p for p in players if _norm(p) not in recent_norm]
    random.shuffle(preferred)

    for p in preferred:
        ph = get_player_photo(drive, p)
        if ph is not None:
            return p, ph

    for p in players:
        ph = get_player_photo(drive, p)
        if ph is not None:
            return p, ph

    return None, None


# ============================================================
# FIXTURES
# ============================================================
def find_opponent(client, team, match_date, occurrence=1):
    ss = with_retry(client.open_by_key, INDEX_SHEET_ID)

    found = 0

    for tab in (FIXTURES_FRIENDLY_TAB, FIXTURES_LEAGUECUP_TAB):
        try:
            ws = ss.worksheet(tab)
        except Exception:
            continue

        data = with_retry(ws.get_all_values)

        for row in data[1:]:
            if len(row) <= FIX_COL_ROUND:
                continue

            if parse_date(row[FIX_COL_DATE]) != match_date:
                continue

            home = clean_team_name(row[FIX_COL_HOME].strip())
            away = clean_team_name(row[FIX_COL_AWAY].strip())
            kickoff = row[FIX_COL_TIME].strip()
            location = row[FIX_COL_LOCATION].strip()
            match_type = row[FIX_COL_MTYPE].strip()
            round_txt = row[FIX_COL_ROUND].strip()

            if home.upper() == team.upper():
                found += 1
                if found == occurrence:
                    return away, match_type, kickoff, location, True, round_txt

            if away.upper() == team.upper():
                found += 1
                if found == occurrence:
                    return home, match_type, kickoff, location, False, round_txt

    return None, None, None, None, None, None


# ============================================================
# STORY VERSION
# ============================================================
def make_story_version(feed_img_path):
    STORY_W, STORY_H = 1080, 1920

    feed = Image.open(feed_img_path).convert('RGB')
    bg = feed.copy()

    scale = max(STORY_W / bg.width, STORY_H / bg.height)
    bg = bg.resize((int(bg.width * scale), int(bg.height * scale)), Image.LANCZOS)

    left = (bg.width - STORY_W) // 2
    top = (bg.height - STORY_H) // 2
    bg = bg.crop((left, top, left + STORY_W, top + STORY_H))
    bg = bg.filter(ImageFilter.GaussianBlur(40))

    fg = feed.copy()
    fscale = min(STORY_W / fg.width, STORY_H / fg.height) * 0.92
    fg = fg.resize((int(fg.width * fscale), int(fg.height * fscale)), Image.LANCZOS)

    bg.paste(fg, ((STORY_W - fg.width) // 2, (STORY_H - fg.height) // 2))

    out = feed_img_path.replace('.png', '_story.png')
    bg.save(out, 'PNG')
    return out


# ============================================================
# BUILD IMAGE
# ============================================================
def build_matchday_image(team, opp_name, we_are_home, kickoff_txt, location_txt,
                         round_txt, player_photo, bg_src, drive, logo_files):

    bg = bg_src.copy().convert('RGBA')
    if bg.size != (MD_W, MD_H):
        bg = bg.resize((MD_W, MD_H))

    draw = ImageDraw.Draw(bg)

    team_font = load_font(TEAM_SIZE)
    info_font = load_font(INFO_SIZE)

    home = team if we_are_home else opp_name
    away = opp_name if we_are_home else team

    def center_y(text, font, cy, fill=WHITE):
        b = draw.textbbox((0, 0), text, font=font)
        w = b[2] - b[0]
        h = b[3] - b[1]
        x = int(TEXT_CX - w / 2 - b[0])
        y = int(cy - h / 2 - b[1])
        draw.text((x, y), text, font=font, fill=fill)

    def resolve_logo(name):
        is_us = is_our_team_name(name)

        lf = find_logo_file(
            logo_files,
            'galaksia praha 23' if is_us else clean_team_name(name)
        )

        if not lf:
            lf = find_logo_file(logo_files, 'no logo')

        if not lf:
            return None

        img = Image.open(io.BytesIO(download_file_bytes(drive, lf['id']))).convert('RGBA')
        img = remove_edge_background(img, tol=60)
        cb = img.getbbox()
        return img.crop(cb) if cb else img

    def paste_logo(logo, cx):
        if logo is None:
            return
        l = logo.copy()
        scale = LOGO_MAX / max(l.width, l.height)
        l = l.resize((max(1, int(l.width * scale)), max(1, int(l.height * scale))), Image.LANCZOS)
        bg.alpha_composite(l, (int(cx - l.width / 2), int(LOGOS_Y - l.height / 2)))

    home_logo = resolve_logo(home)
    away_logo = resolve_logo(away)

    home_full = display_team_for_line(clean_team_name(home))
    away_full = display_team_for_line(clean_team_name(away))

    vs_font = team_font
    vs_gap = 14

    home_size = TEAM_SIZE
    away_size = TEAM_SIZE
    min_team_size = 8

    h_font = load_font(home_size)
    a_font = load_font(away_size)

    def matchup_total_width():
        return (
            text_width(draw, home_full, h_font) +
            vs_gap +
            text_width(draw, 'VS', vs_font) +
            vs_gap +
            text_width(draw, away_full, a_font)
        )

    while matchup_total_width() > TEAM_TEXT_MAX_W and (home_size > min_team_size or away_size > min_team_size):
        home_w = text_width(draw, home_full, h_font)
        away_w = text_width(draw, away_full, a_font)

        if home_w >= away_w and home_size > min_team_size:
            home_size -= 1
            h_font = load_font(home_size)
        elif away_size > min_team_size:
            away_size -= 1
            a_font = load_font(away_size)
        elif home_size > min_team_size:
            home_size -= 1
            h_font = load_font(home_size)
        else:
            break

    total_w = matchup_total_width()
    max_h = max(
        text_height(draw, home_full, h_font),
        text_height(draw, 'VS', vs_font),
        text_height(draw, away_full, a_font)
    )

    x = TEXT_CX - total_w / 2

    for txt, font, add_gap in (
        (home_full, h_font, vs_gap),
        ('VS', vs_font, vs_gap),
        (away_full, a_font, 0),
    ):
        b = draw.textbbox((0, 0), txt, font=font)
        y = TEAM_BLOCK_CY - max_h / 2 - b[1]
        draw.text((int(x - b[0]), int(y)), txt, font=font, fill=WHITE)
        x += (b[2] - b[0]) + add_gap

    paste_logo(home_logo, HOME_LOGO_CX)
    paste_logo(away_logo, AWAY_LOGO_CX)

    info_gap = 10
    sep_w = text_width(draw, '|', info_font)
    
    max_loc_w = int(TEXT_CX - RIGHT_BLOCK_LEFT - sep_w / 2 - info_gap)
    
    loc_font, loc_text = fit_text_font(
        draw,
        location_txt,
        INFO_SIZE,
        max_loc_w,
        min_size=18
    )
    
    draw_axis_centered_segments(
        draw,
        loc_text,
        loc_font,
        '|',
        info_font,
        kickoff_txt,
        info_font,
        INFO_Y,
        gap=info_gap
    )

    if player_photo is not None:
        ph = player_photo.copy()
        cb = ph.info.get('content_bbox', (0, 0, ph.width, ph.height))
        cl, ct, cr, cbottom = cb

        content_h = cbottom - ct
        scale = ((PHOTO_BOTTOM - PHOTO_TOP) / content_h) * 2

        ph = ph.resize((max(1, int(ph.width * scale)), max(1, int(ph.height * scale))), Image.LANCZOS)

        sct = int(ct * scale)
        scl = int(cl * scale)
        scr = int(cr * scale)

        content_cx = (scl + scr) / 2
        box_cx = (PHOTO_LEFT + PHOTO_RIGHT) / 2

        px = int(box_cx - content_cx)
        py = int(PHOTO_TOP - sct)

        bg.alpha_composite(ph, (px, py))

    return bg.convert('RGB')

# ============================================================
# POSTING
# ============================================================
GRAPH = 'https://graph.facebook.com/v20.0'


def load_meta_config():
    with open('meta_config.json') as f:
        return json.load(f)

def _fb_page_photo(page_id, token, image_url, caption, published=True):
    r = requests.post(
        '%s/%s/photos' % (GRAPH, page_id),
        data={
            'url': image_url,
            'caption': caption,
            'published': 'true' if published else 'false',
            'access_token': token
        }
    )
    r.raise_for_status()
    return r.json()


def _fb_story(page_id, token, photo_id):
    r = requests.post(
        '%s/%s/photo_stories' % (GRAPH, page_id),
        data={
            'photo_id': photo_id,
            'access_token': token
        }
    )
    r.raise_for_status()
    return r.json()


def _ig_publish(ig_id, token, image_url, caption=None, is_story=False):
    data = {
        'image_url': image_url,
        'access_token': token
    }

    if is_story:
        data['media_type'] = 'STORIES'
    elif caption:
        data['caption'] = caption

    c = requests.post('%s/%s/media' % (GRAPH, ig_id), data=data)
    c.raise_for_status()
    creation_id = c.json()['id']

    for _ in range(10):
        st = requests.get(
            '%s/%s' % (GRAPH, creation_id),
            params={
                'fields': 'status_code',
                'access_token': token
            }
        )
        code = st.json().get('status_code')
        if code == 'FINISHED':
            break
        if code == 'ERROR':
            raise RuntimeError('IG container error: %s' % st.text)
        time.sleep(3)

    p = requests.post(
        '%s/%s/media_publish' % (GRAPH, ig_id),
        data={
            'creation_id': creation_id,
            'access_token': token
        }
    )
    p.raise_for_status()
    return p.json()


def _get_page_token(page_id, user_token):
    r = requests.get(
        '%s/me/accounts' % GRAPH,
        params={
            'access_token': user_token,
            'limit': 200
        }
    )
    r.raise_for_status()

    for p in r.json().get('data', []):
        if str(p.get('id')) == str(page_id):
            return p['access_token']

    raise RuntimeError('Page %s not found in me/accounts' % page_id)


def post_to_meta(image_path, caption, image_url=None, story_url=None):
    cfg = load_meta_config()
    page_id = cfg['page_id']
    ig_id = cfg['ig_user_id']
    user_token = cfg['page_access_token']

    if not image_url:
        print('    [meta] ERROR: no public image_url provided; cannot post.')
        return

    try:
        token = _get_page_token(page_id, user_token)
    except Exception as e:
        print('    [meta] could not derive Page token: %s' % e)
        token = user_token

    ig_token = user_token

    try:
        _fb_page_photo(page_id, token, image_url, caption, published=True)
        print('    [meta] FB feed OK')
    except Exception as e:
        print('    [meta] FB feed FAILED: %s' % e)

    try:
        su = story_url or image_url
        photo = _fb_page_photo(page_id, token, su, '', published=False)
        _fb_story(page_id, token, photo['id'])
        print('    [meta] FB story OK')
    except Exception as e:
        print('    [meta] FB story FAILED: %s' % e)

    try:
        _ig_publish(ig_id, ig_token, image_url, caption=caption, is_story=False)
        print('    [meta] IG feed OK')
    except Exception as e:
        print('    [meta] IG feed FAILED: %s' % e)

    try:
        _ig_publish(ig_id, ig_token, story_url or image_url, is_story=True)
        print('    [meta] IG story OK')
    except Exception as e:
        print('    [meta] IG story FAILED: %s' % e)


def caption_team_name(name):
    n = (name or '').strip()

    if n.upper() == '11A':
        return 'Galaksia Praha 23'
    if n.upper() == '11B':
        return 'Galaksia Praha 23 B'
    if n.upper() == '11C':
        return 'Galaksia Praha 23 C'

    return clean_team_name(n).title()


def team_partner_line(team):
    team = (team or '').strip().upper()

    if team == '11A':
        return "\nTeam partner: @movetoprague"

    if team == '11B':
        return "\nTeam partner: @coconuculture.eu"

    return ""


def build_matchday_caption(team, opp_name, we_are_home, kickoff_txt, location_txt, round_txt):
    home = team if we_are_home else opp_name
    away = opp_name if we_are_home else team

    matchup = '%s vs %s' % (
        caption_team_name(home),
        caption_team_name(away)
    )

    round_line = ''
    if round_txt:
        rt = round_txt.upper()
        if not rt.startswith('ROUND'):
            rt = 'ROUND ' + rt
        round_line = '🏆 %s\n' % rt.title()

    partner = team_partner_line(team)

    return (
        "⚫️⚪️🟢 MATCH DAY!\n\n"
        "%s\n"
        "%s"
        "🕒 Kick off %s\n"
        "📍 %s\n\n"
        "Come support the boys! 💪%s\n\n"
        "#GalaksiaPraha23 #GP23 #MatchDay #Prague #Praha #PragueFootball "
        "#Fotbal #BlackWhiteGreen #GreenArmy #COYG #FootballFamily"
        % (matchup, round_line, kickoff_txt, location_txt, partner)
    )

# ============================================================
# RUN
# ============================================================
def run():
    args = parse_args()
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    client = get_gspread_client()
    drive = get_drive_service()

    today = datetime.now().date()
    date_str = today.strftime('%Y-%m-%d')

    ss = with_retry(client.open_by_key, LINEUPS_SHEET_ID)
    tabs = [w for w in ss.worksheets() if w.title.strip().upper() in OUR_TEAMS]

    logo_files = list_folder_files(drive, LOGO_FOLDER_ID)

    bg_cache = {}
    generated = 0
    fixture_seen = {}

    for ws in tabs:
        team = ws.title.strip().upper()
        data = with_retry(ws.get_all_values)

        for i, row in enumerate(data[1:], start=2):
            match_date = parse_date(row[COL_MATCH_DATE]) if len(row) > COL_MATCH_DATE else None
            status = row[COL_STATUS].strip() if len(row) > COL_STATUS else ''

            if match_date != today:
                continue

            fixture_key = (team, match_date.isoformat())
            fixture_seen[fixture_key] = fixture_seen.get(fixture_key, 0) + 1
            occurrence = fixture_seen[fixture_key]

            if status:
                print(f'{team} row {i}: already sent, skipping.')
                continue

            starters = split_names(row[COL_STARTERS]) if len(row) > COL_STARTERS else []
            subs = split_names(row[COL_SUBS]) if len(row) > COL_SUBS else []
            players = starters + subs

            opp, match_type, kickoff, location, we_are_home, round_txt = find_opponent(
                client,
                team,
                match_date,
                occurrence=occurrence
            )

            if not opp:
                print(f'{team} row {i}: no fixture found.')
                continue

            if args.post_only:
                safe_team = safe_filename(team)
                out = os.path.join(OUTPUT_DIR, f'matchday_{safe_team}_{date_str}_row{i}.png')
                story_out = out.replace('.png', '_story.png')

                if not os.path.exists(out):
                    print(f'{team} row {i}: missing {out}, cannot post')
                    continue

                if not os.path.exists(story_out):
                    print(f'{team} row {i}: missing {story_out}, cannot post story')
                    continue

                caption = build_matchday_caption(
                    team=team,
                    opp_name=opp,
                    we_are_home=we_are_home,
                    kickoff_txt=kickoff,
                    location_txt=location,
                    round_txt=round_txt
                )

                feed_url = github_raw_url(out)
                story_url = github_raw_url(story_out)

                post_to_meta(
                    out,
                    caption,
                    image_url=feed_url,
                    story_url=story_url
                )

                ws.update_cell(i, COL_STATUS + 1, 'Posted')
                print(f'{team} row {i}: status = Posted')
                generated += 1
                continue

            if team not in bg_cache:
                bg_cache[team] = download_image_by_name(drive, MD_BACKGROUND_NAME_FOR_TEAM[team])

            bg = bg_cache[team]
            if bg is None:
                print(f'{team} row {i}: background missing.')
                continue

            recent = []
            for r in range(i - 1, 1, -1):
                prev = data[r - 1]
                if len(prev) > COL_MD_PICTURE:
                    v = prev[COL_MD_PICTURE].strip()
                    if v:
                        recent.append(v)
                if len(recent) >= RECENT_ROWS:
                    break

            chosen, photo = pick_player_with_photo(drive, players, list(reversed(recent)))
         
            img = build_matchday_image(
                team=team,
                opp_name=opp,
                we_are_home=we_are_home,
                kickoff_txt=kickoff,
                location_txt=location,
                round_txt=round_txt,
                player_photo=photo,
                bg_src=bg,
                drive=drive,
                logo_files=logo_files
            )

            safe_team = safe_filename(team)
            out = os.path.join(OUTPUT_DIR, f'matchday_{safe_team}_{date_str}_row{i}.png')

            img.save(out, 'PNG')
            story_out = make_story_version(out)

            print(f'{team} row {i}: saved {out}')

            if chosen:
                ws.update_cell(i, COL_MD_PICTURE + 1, chosen)
                print(f'{team} row {i}: MD picture = {chosen}')

            if args.generate_only:
                generated += 1
                continue

            if POST_TO_META_ONLINE:
                try:
                    caption = build_matchday_caption(
                        team=team,
                        opp_name=opp,
                        we_are_home=we_are_home,
                        kickoff_txt=kickoff,
                        location_txt=location,
                        round_txt=round_txt
                    )

                    feed_url = github_raw_url(out)
                    story_url = github_raw_url(story_out)

                    print(f'{team} row {i}: feed url: {feed_url}')
                    print(f'{team} row {i}: story url: {story_url}')

                    post_to_meta(
                        out,
                        caption,
                        image_url=feed_url,
                        story_url=story_url
                    )

                    ws.update_cell(i, COL_STATUS + 1, 'Posted')
                    print(f'{team} row {i}: status = Posted')

                except Exception as e:
                    print(f'{team} row {i}: posting failed: {e}')

            generated += 1

    print(f'Done. Generated {generated} image(s).')


if __name__ == '__main__':
    run()
