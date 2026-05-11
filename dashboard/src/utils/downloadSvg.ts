function getBackgroundColor(element: HTMLElement): string {
  const computedStyle = window.getComputedStyle(element);
  let backgroundColor = computedStyle.backgroundColor;

  const isTransparent =
    backgroundColor === 'transparent' ||
    backgroundColor === 'rgba(0, 0, 0, 0)' ||
    (backgroundColor.startsWith('rgba') &&
      (() => {
        const rgbaMatch = backgroundColor.match(/rgba\(([^)]+)\)/);
        if (rgbaMatch) {
          const values = rgbaMatch[1].split(',').map((v) => v.trim());
          const alpha = parseFloat(values[3] || '1');
          return alpha < 0.1;
        }
        return false;
      })());

  if (isTransparent) {
    const parent = element.parentElement;
    if (parent) {
      const parentStyle = window.getComputedStyle(parent);
      backgroundColor = parentStyle.backgroundColor;
    }
  }

  if (
    !backgroundColor ||
    backgroundColor === 'transparent' ||
    backgroundColor === 'rgba(0, 0, 0, 0)' ||
    backgroundColor === ''
  ) {
    return '#121212';
  }

  return backgroundColor;
}

function sanitizeFileName(fileName: string): string {
  const fallback = 'download';
  let name = fileName || fallback;

  name = name.replace(/[/\\?%*:|"<>]/g, '_');

  name = name.replace(/\s+/g, ' ').trim();
  if (!name) {
    name = fallback;
  }
  return name;
}

export function downloadSvgFromContainer(
  container: HTMLElement | null,
  fileName: string
) {
  if (!container) return;

  const svg = container.querySelector('svg');
  if (!svg) return;

  const clonedSvg = svg.cloneNode(true) as SVGSVGElement;

  if (!clonedSvg.getAttribute('xmlns')) {
    clonedSvg.setAttribute('xmlns', 'http://www.w3.org/2000/svg');
  }

  const widthAttr = clonedSvg.getAttribute('width');
  const heightAttr = clonedSvg.getAttribute('height');

  const svgRect = svg.getBoundingClientRect();
  const svgRenderedWidth = svgRect.width;
  const svgRenderedHeight = svgRect.height;
  const containerWidth = container.clientWidth || container.offsetWidth;
  const containerHeight = container.clientHeight || container.offsetHeight;

  let widthNum: number;
  let heightNum: number;
  if (widthAttr && !widthAttr.includes('%')) {
    const parsed = parseFloat(widthAttr);
    widthNum =
      !isNaN(parsed) && parsed > 0
        ? parsed
        : svgRenderedWidth || containerWidth || 800;
  } else {
    widthNum = svgRenderedWidth || containerWidth || 800;
  }
  if (heightAttr && !heightAttr.includes('%')) {
    const parsed = parseFloat(heightAttr);
    heightNum =
      !isNaN(parsed) && parsed > 0
        ? parsed
        : svgRenderedHeight || containerHeight || 350;
  } else {
    heightNum = svgRenderedHeight || containerHeight || 350;
  }

  clonedSvg.setAttribute('width', String(widthNum));
  clonedSvg.setAttribute('height', String(heightNum));

  const backgroundColor = getBackgroundColor(container);

  const backgroundRect = document.createElementNS(
    'http://www.w3.org/2000/svg',
    'rect'
  );
  backgroundRect.setAttribute('width', String(widthNum));
  backgroundRect.setAttribute('height', String(heightNum));
  backgroundRect.setAttribute('fill', backgroundColor);
  backgroundRect.setAttribute('x', '0');
  backgroundRect.setAttribute('y', '0');

  if (clonedSvg.firstChild) {
    clonedSvg.insertBefore(backgroundRect, clonedSvg.firstChild);
  } else {
    clonedSvg.appendChild(backgroundRect);
  }

  const serializer = new XMLSerializer();
  const source = serializer.serializeToString(clonedSvg);
  const blob = new Blob([source], {
    type: 'image/svg+xml;charset=utf-8',
  });

  const url = URL.createObjectURL(blob);
  const safeFileName = sanitizeFileName(fileName);
  const link = document.createElement('a');
  link.href = url;
  link.download = `${safeFileName}.svg`;
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
  URL.revokeObjectURL(url);
}
